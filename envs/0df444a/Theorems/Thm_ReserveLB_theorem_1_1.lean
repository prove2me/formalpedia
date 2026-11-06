-- Prove2me | Theorems.Thm_ReserveLB_theorem_1_1
-- name    : ReserveLB.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:33:54.008988+00:00
-- url     : https://prove2.me/theorems/68bb710f-04a3-4c1f-bbc2-f7aaefa7e6b8
-- title:
--   Theorem 1.1 — randomized polynomial-time strict-budget recourse with expected makespan $\le 909\,\mathrm{LB}_k \le 909\,\mathrm{OPT}_k$
-- statement:
--   Consider $m \ge 1$ related machines with positive rational speeds $s_1, \dots, s_m$, $n \ge 0$ jobs with independent sizes $X_j \ge 0$ whose finite laws are listed as rational atoms with positive probabilities, and a cap $1 \le k \le m$. A reservation $\sigma$ gives every job a nonempty set $\sigma(j)$ of at most $k$ machines before the sizes are known; after they are revealed, every job is moved whole to one of its machines. The benchmark is
--   $$
--   \mathrm{OPT}_k = \min_{\sigma:\ |\sigma(j)| \le k}\ \mathbb E\, T_\sigma(X),\qquad T_\sigma(x) = \min_{\pi:\ \pi(j) \in \sigma(j)}\ \max_i \sum_{j:\ \pi(j) = i}\frac{x_j}{s_i}.
--   $$
--
--   **Theorem.** There are a polynomial $p$ and three algorithms, each running in time polynomial in its binary input:
--   1. $\mathrm{LB}$ computes a rational $\mathrm{LB}_k$ from the instance;
--   2. the construction reads the instance and a string of $p(|\mathrm{enc}(I)|)$ fair coins and writes a reservation and decoder metadata;
--   3. the decoder reads the instance, the construction output and the realized sizes and outputs one machine per job.
--
--   For every well-formed instance: under every coin string, every job reserves at most $k$ distinct machines; under every coin string and every size realization, the decoder sends every job, whole, to one of its reserved machines; $\mathrm{LB}_k \le \mathrm{OPT}_k$; and, with uniform coins independent of the sizes,
--   $$
--   \mathbb E_{\Sigma, X}\, \mathrm{ms}_{\mathrm{decoder}}(\Sigma, X) \le 909\,\mathrm{LB}_k \le 909\,\mathrm{OPT}_k .
--   $$
--
--   The comparator has the same per-job cap; the expectation is that of one global maximum over the coins and the sizes, not a pathwise ratio.
--
--   Differences from the source:
--   - reading: a randomized polynomial-time algorithm; construction coins are independent of future sizes → ∃ polynomial p; construct is TM2-polytime on (instance, coin string); the coins are uniform on the strings of length p(|encInst I|), independent of the sizes, and clauses (a)–(b) hold for every coin string; reason: the paper's randomness is a bounded number of fair bits drawn before the sizes (pp.8, 13)
--   - reading: recourse is polynomial; the output includes metadata for the decoder → decode is a deterministic TM2-polytime map of (instance, construction output, realized sizes); the metadata is the List Bool component of the output; reason: the decoder is one max-flow/slot call per regime with no coins (p.13)
--   - reading: computes LB_k ≤ OPT_k → lb is a deterministic TM2-polytime function of the instance with (lb I : ℝ) ≤ OPT_k; reason: the target search of Section 6.1 is deterministic; a random LB_k would be the weaker reading
--   - encoding: E_{Σ,X}; machines [m], jobs; reservations of at most k distinct machines; the binary input → the average over all coin strings times the exact product-law sum; 0-based indices; reservations as lists with toFinset.card ≤ k; instances as rational lists (malformed inputs may get any output); reason: Lean convention; same instances
--   - encoding: polynomial in the full binary input → Turing.TM2ComputableInPolyTime over fixed binary encodings with the alphabet Fin 4 (numbers in binary, lists length-prefixed); reason: Mathlib's Turing-machine model; binary numbers make the input length the bit size
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Theorem 1.1, p.2; setting, Section 1, p.2

import Mathlib
import Definitions.Def_ReserveLB_Inst
import Definitions.Def_ReserveLB_Inst_WellFormed
import Definitions.Def_ReserveLB_Inst_OPTk
import Definitions.Def_ReserveLB_admissibleRes
import Definitions.Def_ReserveLB_validAssign
import Definitions.Def_ReserveLB_listMakespan
import Definitions.Def_ReserveLB_encInst
import Definitions.Def_ReserveLB_encInstCoins
import Definitions.Def_ReserveLB_encOut
import Definitions.Def_ReserveLB_encDecIn
import Definitions.Def_ReserveLB_encListNat
import Definitions.Def_ReserveLB_coinSizeExpect
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encRat

namespace ReserveLB

/-- **Theorem 1.1 — strict-budget stochastic load balancing with expected makespan `≤ 909 OPT_k`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Theorem 1.1, p.2: "For every input 1 ≤ k ≤ m, a randomized polynomial-time algorithm
computes LBk ≤ OPTk and reserves at most k distinct original machines per job, with
E_(Σ,X) ms_decoder(Σ, X) ≤ 909 LBk ≤ 909 OPTk. Construction and recourse are polynomial in the full
binary input. Construction coins are independent of future sizes. The output includes
polynomial-size endpoint and regime metadata for the decoder." Setting: Section 1, p.2.

There are a polynomial `p` and three maps, each computable by a Turing machine in time polynomial
in the length of its binary input: `lb` (instance ↦ rational), `construct` (instance and a coin
string ↦ reservations and decoder metadata) and `decode` (instance, construction output and
realized sizes ↦ one machine per job), such that for every well-formed instance (`m ≥ 1` positive
rational speeds, `1 ≤ k ≤ m`, finite rational laws):
1. for every coin string of length `p(|enc I|)`, every job gets a nonempty set of at most `k`
   distinct machines;
2. for every such coin string and every realization of the sizes, the decoder sends every job,
   whole, to a machine of its reservation;
3. `LB_k ≤ OPT_k`;
4. the expected makespan of the decoded assignment, over uniform coins and independent sizes, is at
   most `909 LB_k`.

**Formalization Note.** Polynomial time is `Turing.TM2ComputableInPolyTime` over the fixed binary
encodings `encInst`, `encInstCoins`, `encOut`, `encDecIn`, `encListNat`, `encRat`. Randomness is a
uniform coin string of length `p(|encInst I|)` given to the deterministic construction before the
sizes; `lb` and the decoder are deterministic. -/
theorem theorem_1_1 :
    ∃ (p : Polynomial ℕ) (lb : Inst → ℚ)
      (construct : Inst × List Bool → List (List ℕ) × List Bool)
      (decode : (Inst × (List (List ℕ) × List Bool)) × List ℚ → List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encInst OnlineCRS.Combine.encRat lb) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encInstCoins encOut construct) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encDecIn encListNat decode) ∧
      ∀ I : Inst, I.WellFormed →
        (∀ w : List Bool, w.length = p.eval (encInst I).length →
          admissibleRes I.speeds.length I.laws.length I.k (construct (I, w)).1) ∧
        (∀ w : List Bool, w.length = p.eval (encInst I).length →
          ∀ c : (j : Fin I.laws.length) → Fin (I.laws.get j).length,
            validAssign I.laws.length (construct (I, w)).1
              (decode ((I, construct (I, w)), List.ofFn fun j => ((I.laws.get j).get (c j)).1))) ∧
        ((lb I : ℝ) ≤ I.OPTk) ∧
        coinSizeExpect I p (fun w x =>
            listMakespan (fun i : Fin I.speeds.length => ((I.speeds.get i : ℚ) : ℝ))
              (decode ((I, construct (I, w)), x))
              (fun j : Fin I.laws.length => ((x.getD j.val 0 : ℚ) : ℝ)))
          ≤ 909 * (lb I : ℝ) := by sorry

end ReserveLB
