-- Prove2me | Theorems.Thm_PathCount2k_lemma_2_15
-- name    : PathCount2k.lemma_2_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:46:32.802235+00:00
-- url     : https://prove2.me/theorems/3a6c4ce6-0d1a-4cae-8756-97f6b01a8479
-- title:
--   Lemma 2.15 — bounded sampling with at most $4TJ$ fair random bits
-- statement:
--   Let $0<\varepsilon,\delta<1$, $D=k$, and let $R\ge8C_k\varepsilon^{-2}$ and $q=2r+1$ with $r\ge\log_2(2/\delta)$ (Section 2.6 with failure probability $\delta/2$). Put $T=Rq\,kn(1+k^2)$ and $J=\lceil\log_4(2(T+1)/\delta)\rceil$. The amplified finite estimator — groups of $R$ trials of the dynamic program on samples of $\xi$ drawn by the capped rejection sampler, $\hat N=\mathrm{median}(A_1,\dots,A_q)/(R\Gamma)$ with $\Gamma=k!\,k^{k-1}$ — satisfies:
--   1. on every tape it reads at most $4TJ$ fair random bits;
--   2. on a uniformly random tape of $4TJ$ bits,
--   $$
--   \Pr\big[|\hat N-N|\le\varepsilon N\big]\ge1-\delta;
--   $$
--   3. if $N=0$, its output is always zero.
--
--   The capped sampler gives a worst-case bound on the random bits while keeping the accuracy guarantee.
--
--   Differences from the source:
--
--   - generalization: R and q as in Section 2.6 with statistical failure probability δ/2, i.e. R = ⌈8C_kε⁻²⌉, q = 2⌈log₂(2/δ)⌉ + 1 → any R ≥ 8C_kε⁻² and q = 2r + 1 with r ≥ log₂(2/δ); reason: specializes to the paper's choice and to §2.12's R = ⌈216K_kε⁻²⌉
--   - generalization: 2 ≤ k ≤ n (standing assumption of §2.1, p.4) → every k ≥ 1 and every n; reason: the statement is true for these k and n too (k > n gives N = 0); it specializes to the source's range
--   - generalization: a directed graph (no self-loops discussed) → the arc set may contain self-loops (v, v); reason: a path never uses a loop, so P_k and N are unchanged; on loop-free graphs the statement is the source's
--   - reading: the amplified finite estimator can be implemented using at most 4TJ fair random bits → the explicit program amplify (§2.12 steps 3–4 with the capped sampler of the proof) reads at most 4TJ tape bits on every tape, and the probability is the fraction of the 2^{4TJ} tapes; reason: the paper's implementation, made explicit; the output median(A)/(RΓ) is the median of the group means, as the paper notes
--   - encoding: fair random bits; ξ decoded from accepted 4-bit values; a graph with m arcs → a tape ℕ → Bool read left to right (false past 4TJ); the decoding table 0–5 ↦ 0, 6–7 ↦ 1, 8–9 ↦ −1, 10 ↦ 2, 11 ↦ −2; the arc list A without repetitions, E = A.toFinset; reason: same law of each draw (6, 2, 2, 1, 1 of 12 accepted values); every arc set is A.toFinset of such a list
--   - encoding: vertices v ∈ V, positions and coordinates 1, …, k → vertices Fin n, positions and coordinates Fin k (0-based); reason: relabelling; same instances
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Lemma 2.15 and its proof, p.14

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_DP
import Definitions.Def_PathCount2k_Algorithm

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace PathCount2k

/-- Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), with Extensions to Counting
Bounded Treewidth Graphs and Multilinear Monomials*, STOC 2027 submission manuscript (Nov 2026), **Lemma 2.15** (Bounded sampling), p.14: "Let `0 < ε, δ < 1`, set `D = k`, and
choose `R` and `q` as in Section 2.6, with statistical failure probability `δ/2`. Put
`T = Rq kn(1+k²)` and `J = ⌈log₄(2(T+1)/δ)⌉`. The amplified finite estimator can be implemented using
at most `4TJ` fair random bits, with output `N̂` satisfying `Pr[|N̂ − N| ≤ εN] ≥ 1 − δ`. If `N = 0`,
the output is always zero."

The implementation is `amplify` (§2.12 steps 3–4 with the capped sampler of the proof of
Lemma 2.15, `Γ = k! k^{k−1}`), run on a tape of fair bits. For any `R ≥ 8C_k ε⁻²` and
`q = 2r + 1` with `r ≥ log₂(2/δ)`:
1. on every tape it reads at most `4TJ` bits;
2. on a uniformly random tape of `4TJ` bits, `Pr[|N̂ − N| ≤ εN] ≥ 1 − δ`;
3. if `N = 0` its output is `0` on every tape.

**Formalization Note.** The probability is the fraction of the `2^{4TJ}` tapes of length `4TJ`,
read as `false` beyond; the graph is the arc list `A` without repetitions, `E = A.toFinset`. The
paper's choice ("as in Section 2.6, with statistical failure probability `δ/2`") is
`R = ⌈8C_k ε⁻²⌉`, `r = ⌈log₂(2/δ)⌉`, and §2.12 uses `R = ⌈216 K_k ε⁻²⌉ ≥ 8C_k ε⁻²`; both are
instances. Stated for every `k ≥ 1` and `n` (the paper assumes `2 ≤ k ≤ n`, §2.1). -/
theorem lemma_2_15 (n : ℕ) (A : List (Fin n × Fin n)) (hA : A.Nodup) (k : ℕ) (hk : 1 ≤ k)
    (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (R r : ℕ)
    (hR : 8 * Ck k / ε ^ 2 ≤ (R : ℝ)) (hr : Real.logb 2 (2 / δ) ≤ (r : ℝ)) :
    let q : ℕ := 2 * r + 1
    let T : ℕ := R * q * k * n * (1 + k ^ 2)
    let J : ℕ := ⌈Real.logb 4 (2 * ((T : ℝ) + 1) / δ)⌉₊
    (∀ t : ℕ → Bool, ((amplify n k A R q J (Gamma k) t).run 0).1.2 ≤ 4 * T * J) ∧
      (((Finset.univ.filter fun b : Fin (4 * T * J) → Bool =>
          |((amplify n k A R q J (Gamma k)
              (fun i => if h : i < 4 * T * J then b ⟨i, h⟩ else false)).run 0).1.1 -
            (N n A.toFinset k : ℝ)| ≤ ε * (N n A.toFinset k : ℝ)).card : ℝ) /
          2 ^ (4 * T * J) ≥ 1 - δ) ∧
      (N n A.toFinset k = 0 → ∀ t : ℕ → Bool, ((amplify n k A R q J (Gamma k) t).run 0).1.1 = 0) := by sorry

end PathCount2k
