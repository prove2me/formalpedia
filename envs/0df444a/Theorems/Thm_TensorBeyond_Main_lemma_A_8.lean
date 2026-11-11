-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_A_8
-- name    : TensorBeyond.Main.lemma_A_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:13.837279+00:00
-- url     : https://prove2.me/theorems/6e191cbc-7788-4284-9dcf-a0892e31f956
-- title:
--   Lemma A.8 — a degree-$O(1)$ relaxation certifies $\tilde{\mathbb E}[\sum_i\langle v_i,x\rangle^6]\le n^6(1+\tilde O(\sqrt{m/n^3}))$
-- statement:
--   In this item $\langle\cdot,\cdot\rangle$ is the unnormalized dot product of Appendix A. Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes3}$, and consider the constraints of step 1 of Algorithm 1 for $k=3$ with slack $\xi=Kn^{3/2}\sqrt{m\log m}$:
--   $$\sum_i (v_i^\top x)^3\ \ge\ n^3-Kn^{3/2}\sqrt{m\log m},\qquad (s^\top x)^2\le0.01\,n^2\ (s\in S),\qquad x_u^2=1 .$$
--   For every $K,c>0$ there are $C,D>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le\sqrt{n^3\ell}/(\log n)^C$ (the model of Section 5.1 for $k=3$), with probability at least $1-n^{-c}$, for every finite list $S\subset\mathbb R^n$ every pseudo-expectation of degree $D$ satisfying these constraints has
--   $$\tilde{\mathbb E}\Big[\sum_i (v_i^\top x)^6\Big]\ \le\ n^6\Big(1+(\log n)^D\sqrt{m/n^3}\Big).$$
--   It is the upper bound on the sixth moment used in Lemmas 6.3 and 7.16.
--
--   Differences from the source:
--   - encoding: ⟨v_i, x⟩ → unnormalized v_iᵀx; reason: Appendix A's convention, under which the bound n⁶ is stated
--   - reading: "ξ = O(n^{3/2}√(m log m))", "constraints as in step 1 of Algorithm 5.1" → for every K > 0 the inequality Σ_i(v_iᵀx)³ ≥ n³ − K n^{3/2}√(m log m), for every finite list S the constraints (sᵀx)² ≤ 0.01n², and x_u² = 1; reason: O(·) with any constant, and every step of the algorithm
--   - reading: degree O(1), Õ(√(m/n³)), "1 − 1/poly(n)" → degree D, (log n)^D √(m/n³), probability ≥ 1 − n^{−c} for every c; reason: the paper's conventions, with "for every c" the stronger reading
--   - reading: "T sampled as described in Section 5.1" → for every c there are C, N₀ with ℓ ≥ 1, ℓ ≤ n/(log n)^C, n ≤ m ≤ √(n³ℓ)/(log n)^C; reason: §5.1 with k = 3 (ℓ = õ(n), m = õ(n^{3/2}ℓ^{1/2})) and the standing n ≤ m of §4.1, as in Theorem 7.1; ℓ is the SoS level (positive in Theorem 7.1)
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 64 (PDF 66), Lemma A.8

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma A.8 (unnormalized dot product): for every `K, c > 0` there are `C, D > 0` and `N₀` such
that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with `ℓ ≤ n/(log n)^C` and `m ≤ √(n³ℓ)/(log n)^C` (the
model of Section 5.1 for `k = 3`), with probability at least `1 − n^{−c}`, for every list `S` of
found vectors, every pseudo-expectation of degree `D` satisfying step 1 of Algorithm 1
(`n³⟨T, x^{⊗3}⟩ ≥ n³ − K n^{3/2}√(m log m)`, `(sᵀx)² ≤ 0.01 n²` for `s ∈ S`, `x_u² = 1`) has
`Ẽ[∑_i (v_iᵀx)⁶] ≤ n⁶ (1 + (log n)^D √(m/n³))`. -/
theorem lemma_A_8 (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 3 * (ℓ : ℝ)) / Real.log (n : ℝ) ^ C →
      1 - (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        ∀ (S : List (Fin n → ℝ)) (E : Poly n →ₗ[ℝ] ℝ), IsPseudoExp D (prog3 v K S) E →
          E (Tpow v 6) ≤
            (n : ℝ) ^ 6 * (1 + Real.log (n : ℝ) ^ D * Real.sqrt ((m : ℝ) / (n : ℝ) ^ 3))) := by sorry

end TensorBeyond.Main
