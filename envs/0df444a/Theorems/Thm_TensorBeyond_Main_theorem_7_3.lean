-- Prove2me | Theorems.Thm_TensorBeyond_Main_theorem_7_3
-- name    : TensorBeyond.Main.theorem_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:14.237197+00:00
-- url     : https://prove2.me/theorems/ea7a0662-5f08-4e01-818c-b554300a303b
-- title:
--   Theorem 7.3 — a degree-$\tilde O(\ell)$ relaxation certifies $\tilde{\mathbb E}[h_4(x)]\le mn^{3.5}/\sqrt\ell$
-- statement:
--   In this item $\langle\cdot,\cdot\rangle$ is the unnormalized dot product of Section 7. Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes3}$, and
--   $$h_4(x)=\sum_{i\ne j}(v_i^\top v_j)\,(v_i^\top x)^2\,(v_j^\top x)^2 .$$
--   For every $K,c>0$ there are $C,D>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le\sqrt{n^3\ell}/(\log n)^C$, with probability at least $1-n^{-c}$, for every finite list $S\subset\mathbb R^n$ every pseudo-expectation of degree $D\ell(\log n)^D$ satisfying step 1 of Algorithm 1 ($\sum_i(v_i^\top x)^3\ge n^3-Kn^{3/2}\sqrt{m\log m}$, $(s^\top x)^2\le0.01n^2$ for $s\in S$, $x_u^2=1$) has
--   $$\tilde{\mathbb E}[h_4(x)]\ \le\ \frac{m\,n^{3.5}}{\sqrt\ell}.$$
--   This is the paper's main technical bound for $k=3$, obtained from spectral norms of level-$\ell$ Kikuchi matrices; it controls the noise term in the Cauchy–Schwarz step of Lemma 7.16.
--
--   Differences from the source:
--   - encoding: ⟨v_i, v_j⟩, ⟨v_i, x⟩ → unnormalized v_iᵀv_j, v_iᵀx; reason: Section 7's convention, under which the bound m n^{3.5}/√ℓ is stated
--   - reading: "T sampled as described in Section 5.1" → ℓ ≤ n/(log n)^C, n ≤ m ≤ √(n³ℓ)/(log n)^C for every c with C, N₀; reason: §5.1 with k = 3 (ℓ = õ(n), m = õ(n^{3/2}ℓ^{1/2})) and the standing n ≤ m of §4.1, as in Theorem 7.1
--   - reading: "ξ = O(n^{3/2}√(m log m))", "constraints as in step 1 of Algorithm 5.1" → for every K > 0 the inequality Σ_i(v_iᵀx)³ ≥ n³ − K n^{3/2}√(m log m), for every finite list S the constraints (sᵀx)² ≤ 0.01n², and x_u² = 1; reason: O(·) with any constant, and every step of the algorithm
--   - reading: degree Õ(ℓ), "1 − 1/poly(n)" → degree D·ℓ·(log n)^D, probability ≥ 1 − n^{−c} for every c; reason: the paper's conventions, with "for every c" the stronger reading
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: Theorem 7.1 takes positive integers; √ℓ is in the denominator
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 41 (PDF 43), Theorem 7.3

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Theorem 7.3 (unnormalized dot product): for every `K, c > 0` there are `C, D > 0` and `N₀`
such that for all `n ≥ N₀`, `ℓ ≥ 1`, `n ≤ m` with `ℓ ≤ n/(log n)^C` and
`m ≤ √(n³ℓ)/(log n)^C`, with probability at least `1 − n^{−c}`, for every list `S` of found
vectors, every pseudo-expectation of degree `D ℓ (log n)^D` satisfying step 1 of Algorithm 1 has
`Ẽ[h_4(x)] ≤ m n^{3.5}/√ℓ`. -/
theorem theorem_7_3 (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 3 * (ℓ : ℝ)) / Real.log (n : ℝ) ^ C →
      1 - (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        ∀ (S : List (Fin n → ℝ)) (E : Poly n →ₗ[ℝ] ℝ),
          IsPseudoExp (D * (ℓ : ℝ) * Real.log (n : ℝ) ^ D) (prog3 v K S) E →
          E (hNoise v 2) ≤ (m : ℝ) * (n : ℝ) ^ ((7 : ℝ) / 2) / Real.sqrt (ℓ : ℝ)) := by sorry

end TensorBeyond.Main
