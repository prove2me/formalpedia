-- Prove2me | Theorems.Thm_PairwiseRealize_theorem_2_1
-- name    : PairwiseRealize.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:59.681649+00:00
-- url     : https://prove2.me/theorems/4c87bcbb-1e52-4bee-b202-9da81a80e769
-- title:
--   Theorem 2.1, p.4 — robust interior realization: targets of depth $Cn^2\log(n+1)$ are exactly realizable avoiding $2^n/4096$ rows, by a Las Vegas algorithm in time polynomial in $2^n$
-- statement:
--   **Robust interior realization.** There are an absolute constant $C$, a threshold $n_0$, one randomized machine $M$, and constants $C',d$ such that the following holds for every $n\ge n_0$. Let $D\subseteq V=\{0,1\}^n$ be any forbidden set with $|D|\le N/4096$, $N=2^n$, and let $U=V\setminus D$. Let $b\in\mathbb Z^m$ be an integer target whose centered vector $y_U=2Tb-\sum_{x\in U}v_x$ lies in $P_U$ and satisfies
--
--   $$\operatorname{depth}_U(y_U)\ge Cn^2\log(n+1).$$
--
--   Then:
--
--   1. $b$ has an exact realization: a set $S\subseteq U$ of distinct rows with $\sum_{x\in S}w_x=b$;
--   2. on input $(n,\text{membership table of }D,b)$, every run of $M$ that has halted shows the membership table of an exact realization of $b$ in $U$, whatever the random bits;
--   3. $M$ halts with probability one;
--   4. the expected number of steps of $M$ is finite and at most $C'N^d$.
--
--   The depth condition is a promise on the input; the machine is constrained only on promise inputs. In words: fractional feasibility together with a little slack, polylogarithmic in the table length, is enough for an exact integer realization by distinct rows, even after an adversary removes a small constant fraction of the rows, and a realization can be found in time polynomial in the table length.
--
--   **Formalization Note** The machine is the published randomized Post–Turing machine `OAI.MatchingFPRAS.RandomMachine` (one finite transition table, one tape operation and one fair bit per step). `haltMass M input t` is the probability that the run has halted after $t$ bits, and the expected number of steps is the tail sum $\sum_t(1-\text{haltMass})$.
--
--   Differences from the source:
--   - reading: "a Las Vegas algorithm finds such a realization in expected polynomial bit time in N" → one RandomMachine, all n ≥ n₀, correct on every halted bit prefix, haltMass → 1, Σ_t (1 − haltMass t) summable and ≤ C′(2ⁿ)^d; reason: the published machine states exactly these semantics; a step is one bit operation and one random bit, and the tail sum is the expected step count
--   - encoding: "its explicit membership table and the target b" → `inputCode`: n in binary, the table of D (symbols 2/1, delimiter 3), the coordinates of b as signed binary numerals; the output is the table of S; reason: n is the binary logarithm of the table length, so no instance changes
--   - encoding: log(n + 1), base unspecified → the natural logarithm; reason: another base changes only C
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), Theorem 2.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_ContingencyTables
import Definitions.Def_PairwiseRealize_Model
import Definitions.Def_PairwiseRealize_Machine

namespace PairwiseRealize

open OAI.MatchingFPRAS OAI.ContingencyTables.Algorithms

/-- **Theorem 2.1 (Robust interior realization), p.4 (PDF p.5).** K. Shi, H. Sun, *Robust Exact
Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…):
"There is an absolute constant C such that, for all sufficiently large n, the following holds. Let
D ⊆ V be any forbidden set with |D| ≤ εN, where ε = 1/4096, and let U = V ∖ D. Every integer target
b ∈ ℤ^m whose centered vector y_U from (2.3) lies in P_U and satisfies depth_U(y_U) ≥ Cn² log(n + 1)
has an exact realization by distinct rows from U. Given D by its explicit membership table and the
target b, a Las Vegas algorithm finds such a realization in expected polynomial bit time in N."
"The depth condition is a promise on the input; the algorithm verifies the returned table exactly.
The input consists of the integer target and the explicit membership table of D."

There are `C`, `n₀`, one machine `M` and constants `C', d` such that for every `n ≥ n₀`, every
`D ⊆ V` with `|D| ≤ 2ⁿ/4096` and every integer target `b` with `y_U ∈ P_U` and
`depth_U(y_U) ≥ Cn² log(n + 1)` (`U = V ∖ D`):
1. `b` has an exact realization `S ⊆ U`;
2. on input `(n, table of D, b)`, every run of `M` that has halted shows the membership table of an
   exact realization `S ⊆ U` of `b` (Las Vegas: never a wrong answer);
3. `M` halts with probability one;
4. the expected number of steps, `Σ_t P(not halted after t steps)`, is finite and at most
   `C' N^d`, `N = 2ⁿ`.

**Formalization Note** "A Las Vegas algorithm" is one machine for all `n` (a randomized Post–Turing
machine, the published `OAI.MatchingFPRAS.RandomMachine`: a finite transition table, one tape
operation and one fair bit per step); "bit time" is its number of steps; `haltMass M input t` is the
probability that the run on `t` fair bits has halted, so the tail sum is the expected running time.
The machine is constrained only on promise inputs, as the paper says. `log` is the natural
logarithm (another base changes only `C`). The ball in the depth is Euclidean (`depth`). -/
theorem theorem_2_1 :
    ∃ C : ℝ, ∃ n₀ : ℕ, ∃ (M : RandomMachine) (C' d : ℕ),
      ∀ n ≥ n₀, ∀ D : Finset (Row n), 4096 * D.card ≤ 2 ^ n →
      ∀ b : Feat n → ℤ,
        centered n (Finset.univ \ D) b ∈ zonotope n (Finset.univ \ D) →
        C * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1) ≤
          depth n (Finset.univ \ D) (centered n (Finset.univ \ D) b) →
        (∃ S, IsRealization n (Finset.univ \ D) b S) ∧
        (∀ (t : ℕ) (bits : Fin t → Bool), (run M (inputCode n D b) bits).state = none →
          ∃ S, IsRealization n (Finset.univ \ D) b S ∧ OutputsSet M (inputCode n D b) bits n S) ∧
        Filter.Tendsto (haltMass M (inputCode n D b)) Filter.atTop (nhds 1) ∧
        Summable (fun t => 1 - haltMass M (inputCode n D b) t) ∧
        ∑' t, (1 - haltMass M (inputCode n D b) t) ≤ (C' : ℝ) * ((2 : ℝ) ^ n) ^ d := by sorry

end PairwiseRealize
