-- Prove2me | Theorems.Thm_PunctSketch_theorem_6
-- name    : PunctSketch.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:49.609937+00:00
-- url     : https://prove2.me/theorems/eafa2c72-90c0-4fd0-a1b7-a97405221eb2
-- title:
--   Theorem 6, p.15, with Result 1, p.2 — public-coin $k$-connectivity in $O(k\log^3n)$ bits per vertex, turnstile streaming in $O(kn\log^3n)$ bits
-- statement:
--   For every real $c>0$ both of the following hold.
--
--   **(i) Distributed sketching with public coins.** There are a constant $A>0$, an exponent $a$, sizes $N,M,L$ and two polynomial-time machines, one for the node players and one for the coordinator, such that for all $1\le k<n$:
--
--   1. the coins are uniform on $\{0,\dots,M-1\}^N$ with $1\le M\le n^a$, $N\le n^a$;
--   2. every message has exactly $L\le A\,k\log_2^3n$ bits, and depends only on $n,k$, the player's identifier, its neighbourhood and the coins;
--   3. for every graph $G$ on $n$ vertices,
--   $$\Pr[\text{the coordinator's output is not a correct certificate for }G]\le n^{-c}.$$
--
--   A correct certificate gives the answer, a witness set $Z$ with $|Z|<k$ for "no", and a spanning subgraph $H$ with at most $kn-\binom{k+1}2$ edges that preserves connectivity after every deletion of fewer than $k$ vertices.
--
--   **(ii) One-pass turnstile streaming.** There are a constant $A>0$, an exponent $a$, sizes $N,M,S$ and polynomial-time machines for initialization, update and output, where only the initializer reads the coins, such that for all $1\le k<n$: the coins are as above, the memory has exactly $S\le A\,k\,n\log_2^3n$ bits throughout, and for every valid stream $\sigma$, fixed before the coins,
--   $$\Pr[\text{the output differs from "the final graph of }\sigma\text{ is }k\text{-connected"}]\le n^{-c}.$$
--
--   Theorem 6 as printed, and Result 1, follow at once. The constants and the machines depend on $c$ only.
--
--   **Formalization Note** One machine serves all $(n,k)$, and every machine input writes $n$ in unary, so polynomial time means polynomial in $n$, $k$ and the input.
--
--   Differences from the source:
--   - reading: "with high probability", "at most 1/poly(n)" → for every c > 0, error at most n^{−c}, with constants and machines chosen after c; reason: the proof scales: fingerprint parameter k + 5 + a and R = 10(a+1)g give n^{−(3+a)}
--   - reading: a protocol, an algorithm, "poly(n, k) time" → Mathlib TM2 machines, one for all (n, k), with n in unary in every input and coins uniform on Fin N → Fin M, 1 ≤ M, N and M polynomial; the coordinator reads the public coins; reason: uniformity gives "polynomial time" its content; unary n because the bound is in n; the paper draws from 𝔽_Q ∖ {0}, which fair bits cannot produce exactly; p.16 computes the fingerprint from 𝒓
--   - reading: "solve the k-vertex connectivity problem" (Theorem 6), "compute their answer and certify it" (Result 1) → clause (i) outputs a certificate with the edge bound of §5.4 and the agreement for all |F| < k; clause (ii) outputs the answer; reason: Result 1 and §5.4 give the certificate for the protocol; Theorem 6 asks only for the answer in clause (ii)
--   - generalization: "n is large enough" (p.4), k = o(n/log³ n) (footnote 7) → every 1 ≤ k < n, with no threshold on n; reason: for small n and large k each vertex sends its neighbourhood (footnote 7), which the bound on L allows; the printed theorem is a special case
--   - generalization: the theorem bounds bits and the coordinator’s time only → polynomial-time encoders, initializer and update as well; exact message and memory length; reason: p.20: "Each node performs polynomially many field operations"; uniform update also rules out hard-wiring seeds, so that randomness must really be stored as on p.19; an exact length implies the worst-case bound
--   - encoding: V = [n], N(x) a set, unordered pairs, an output graph and set → Fin n, bit masks of length n, an output string with exact lengths parsed by IsCertificate; reason: Lean convention; a malformed output is not a certificate
--   - encoding: turnstile stream: edge insertions and deletions from the empty graph → IsValidStream: distinct endpoints, insert only an absent edge, delete only a present edge, any length; reason: the model of p.1; a list of updates fixed before the coins
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Theorem 6, p.15 (PDF p.16); Result 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_PunctSketch_EncInput
import Definitions.Def_PunctSketch_DecInput
import Definitions.Def_PunctSketch_InitInput
import Definitions.Def_PunctSketch_UpdInput
import Definitions.Def_PunctSketch_OutInput
import Definitions.Def_PunctSketch_coinList
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_PunctSketch_nbrMask
import Definitions.Def_PunctSketch_IsCertificate
import Definitions.Def_PunctSketch_IsValidStream
import Definitions.Def_PunctSketch_runStream

namespace PunctSketch

/-- **Theorem 6 with Result 1.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Theorem 6, p.15: "There exists: (i) a distributed sketching protocol
with public randomness and O(k log³ n) bits of communication per node, and (ii) a one-pass turnstile
streaming algorithm with O(kn log³ n) bits of space complexity that solve the k-vertex connectivity
problem with high probability." Result 1, p.2: "the coordinator errs with probability at most 1/ poly(n).
The coordinator needs only poly(n, k) time to compute their answer and certify it."

For every `c > 0`, for all `1 ≤ k < n`:

(i) one pair of polynomial-time machines `enc`, `dec`, with coins uniform on `Fin N → Fin M` of polynomial
size: every message has exactly `L ≤ A k log₂³ n` bits, a player reads only `n, k`, its own ID, its
neighbourhood and the coins, and for every graph `G` the coordinator's output fails to be a correct
certificate with probability at most `n^{−c}`;

(ii) polynomial-time machines `init`, `upd`, `out`, where only `init` reads coins: the memory has exactly
`S ≤ A k n log₂³ n` bits, and for every valid stream, fixed before the coins, the output differs from
"the final graph is `k`-connected" with probability at most `n^{−c}`.

**Formalization Note.** "With high probability" is every polynomial, with the constants and the machines
chosen after `c` and before `n, k`. One machine serves all `(n, k)`, and every input writes `n` in unary, so
"polynomial time" is polynomial in `n`, `k` and the input. The coins are uniform on a finite alphabet of size
`M ≥ 1`, since the paper draws from `𝔽_Q ∖ {0}`. The coordinator reads the public coins (p.16). No threshold
on `n` is assumed. -/
theorem theorem_6 (c : ℝ) (hc : 0 < c) :
    (∃ (A : ℝ) (a : ℕ) (N M L : ℕ → ℕ → ℕ) (enc : EncInput → List Bool) (dec : DecInput → List Bool),
      0 < A ∧
      Nonempty (Turing.TM2ComputableInPolyTime EncInput.code encBits enc) ∧
      Nonempty (Turing.TM2ComputableInPolyTime DecInput.code encBits dec) ∧
      ∀ n k : ℕ, 1 ≤ k → k < n →
        1 ≤ M n k ∧ M n k ≤ n ^ a ∧ N n k ≤ n ^ a ∧
        (L n k : ℝ) ≤ A * k * Real.logb 2 n ^ 3 ∧
        (∀ (v : Fin n) (S : Fin n → Bool) (ω : Fin (N n k) → Fin (M n k)), S v = false →
          (enc ⟨n, k, v, List.ofFn S, coinList ω⟩).length = L n k) ∧
        ∀ G : SimpleGraph (Fin n),
          coinProb (fun ω : Fin (N n k) → Fin (M n k) =>
            ¬ IsCertificate G k
              (dec ⟨n, k, coinList ω,
                List.ofFn (fun v : Fin n => enc ⟨n, k, v, nbrMask G v, coinList ω⟩)⟩)) ≤
            (n : ℝ) ^ (-c)) ∧
    (∃ (A : ℝ) (a : ℕ) (N M S : ℕ → ℕ → ℕ) (init : InitInput → List Bool)
        (upd : UpdInput → List Bool) (out : OutInput → Bool),
      0 < A ∧
      Nonempty (Turing.TM2ComputableInPolyTime InitInput.code encBits init) ∧
      Nonempty (Turing.TM2ComputableInPolyTime UpdInput.code encBits upd) ∧
      Nonempty (Turing.TM2ComputableInPolyTime OutInput.code (fun b : Bool => encBits [b]) out) ∧
      ∀ n k : ℕ, 1 ≤ k → k < n →
        1 ≤ M n k ∧ M n k ≤ n ^ a ∧ N n k ≤ n ^ a ∧
        (S n k : ℝ) ≤ A * k * n * Real.logb 2 n ^ 3 ∧
        (∀ ω : Fin (N n k) → Fin (M n k), (init ⟨n, k, coinList ω⟩).length = S n k) ∧
        (∀ (s : List Bool) (u v : Fin n) (b : Bool), s.length = S n k → u ≠ v →
          (upd ⟨n, k, s, u, v, b⟩).length = S n k) ∧
        ∀ σ : List (Update n), IsValidStream σ →
          coinProb (fun ω : Fin (N n k) → Fin (M n k) =>
            ¬ (out ⟨n, k, runStream upd n k (init ⟨n, k, coinList ω⟩) σ⟩ = true ↔
              Balinski61.Connectivity.IsNTuplyConnected (streamGraph σ) k)) ≤
            (n : ℝ) ^ (-c)) := by sorry

end PunctSketch
