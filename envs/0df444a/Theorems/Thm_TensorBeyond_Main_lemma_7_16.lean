-- Prove2me | Theorems.Thm_TensorBeyond_Main_lemma_7_16
-- name    : TensorBeyond.Main.lemma_7_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:15:19.949888+00:00
-- url     : https://prove2.me/theorems/6086c0ec-be79-4586-bda6-4b88f9623dee
-- title:
--   Lemma 7.16 — the premise of Lemma 5.3 for $k=3$: $\tilde{\mathbb E}[n^{-6}T_6]\ge1-\varepsilon$, $\tilde{\mathbb E}[n^{-4}T_4]\le1+\varepsilon$
-- statement:
--   In this item $\langle\cdot,\cdot\rangle$ is the unnormalized dot product of Section 7. Let $v_1,\dots,v_m$ be i.i.d. uniform in $\{\pm1\}^n$, $T=\sum_iv_i^{\otimes3}$ and $T_t(x)=\sum_i(v_i^\top x)^t$. For every $\varepsilon\in(0,1)$ and $K,c>0$ there are $C,D>0$ and $N_0$ such that for all $n\ge N_0$, $\ell\ge1$ and $n\le m$ with $\ell\le n/(\log n)^C$ and $m\le\sqrt{n^3\ell}/(\log n)^C$, with probability at least $1-n^{-c}$, for every finite list $S\subset\mathbb R^n$ (that is, at every step of the algorithm) every pseudo-expectation of degree $D\ell(\log n)^D$ satisfying step 1 of Algorithm 1 ($T_3(x)\ge n^3-Kn^{3/2}\sqrt{m\log m}$, $(s^\top x)^2\le0.01n^2$ for $s\in S$, $x_u^2=1$) has
--   $$\tilde{\mathbb E}\Big[\frac1{n^6}\sum_i(v_i^\top x)^6\Big]\ \ge\ 1-\varepsilon,\qquad \tilde{\mathbb E}\Big[\frac1{n^4}\sum_i(v_i^\top x)^4\Big]\ \le\ 1+\varepsilon .$$
--   These are the premises of Lemma 5.3 with $d=4$, which make the rounding succeed at every step for $k=3$.
--
--   Differences from the source:
--   - encoding: ⟨v_i, x⟩ → unnormalized v_iᵀx; reason: Section 7's convention, under which the normalizations 1/n⁶ and 1/n⁴ are stated
--   - generalization: "at every step of the algorithm" → for every finite list S of previously found vectors; reason: the found vectors at every step form such a list, so the statement covers every step without modelling the algorithm
--   - reading: "T sampled as described in Section 5.1", "1 − 1/poly(n)", degree Õ(ℓ) of Theorem 7.3 → ℓ ≤ n/(log n)^C, n ≤ m ≤ √(n³ℓ)/(log n)^C, probability ≥ 1 − n^{−c} for every c, degree D·ℓ·(log n)^D; reason: §5.1 with k = 3 and the standing n ≤ m of §4.1, with "for every c" the stronger reading
--   - reading: the constraints of step 1 with ξ = O(n^{3/2}√(m log m)) → for every K > 0 the inequality T_3(x) ≥ n³ − K n^{3/2}√(m log m); reason: O(·) with any constant
--   - reading: ε "its input-error parameter" → ε ∈ (0, 1) fixed before n, m, ℓ; reason: the proof calls ε "an absolute constant independent of m, n, and ℓ"
--   - reading: ℓ unconstrained below → 1 ≤ ℓ; reason: Theorem 7.1 takes positive integers
-- source:
--   Jha, Mazzali, Xu, Tensor Decomposition Beyond the Spectral Threshold, STOC 2027 submission (held manuscript, sha256 988d801c…), p. 54 (PDF 56), Lemma 7.16

import Mathlib
import Definitions.Def_TensorBeyond_Main_Model
import Definitions.Def_TensorBeyond_Main_SoS
import Definitions.Def_TensorBeyond_Main_Polys

set_option autoImplicit false

namespace TensorBeyond.Main

/-- Lemma 7.16 (unnormalized dot product; premise of Lemma 5.3 for `k = 3`, `d = 4`): for every
`ε ∈ (0, 1)` and `K, c > 0` there are `C, D > 0` and `N₀` such that for all `n ≥ N₀`, `ℓ ≥ 1`,
`n ≤ m` with `ℓ ≤ n/(log n)^C` and `m ≤ √(n³ℓ)/(log n)^C`, with probability at least `1 − n^{−c}`,
for every list `S` of found vectors (every step of the algorithm), every pseudo-expectation of
degree `D ℓ (log n)^D` satisfying step 1 of Algorithm 1 has
`Ẽ[n^{−6} ∑_i (v_iᵀx)⁶] ≥ 1 − ε` and `Ẽ[n^{−4} ∑_i (v_iᵀx)⁴] ≤ 1 + ε`. -/
theorem lemma_7_16 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ N₀ : ℕ, ∀ n m ℓ : ℕ, N₀ ≤ n → 1 ≤ ℓ → n ≤ m →
      (ℓ : ℝ) ≤ (n : ℝ) / Real.log (n : ℝ) ^ C →
      (m : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 3 * (ℓ : ℝ)) / Real.log (n : ℝ) ^ C →
      1 - (n : ℝ) ^ (-c) ≤ probV n m (fun v =>
        ∀ (S : List (Fin n → ℝ)) (E : Poly n →ₗ[ℝ] ℝ),
          IsPseudoExp (D * (ℓ : ℝ) * Real.log (n : ℝ) ^ D) (prog3 v K S) E →
          1 - ε ≤ E (MvPolynomial.C (1 / (n : ℝ) ^ 6) * Tpow v 6) ∧
          E (MvPolynomial.C (1 / (n : ℝ) ^ 4) * Tpow v 4) ≤ 1 + ε) := by sorry

end TensorBeyond.Main
