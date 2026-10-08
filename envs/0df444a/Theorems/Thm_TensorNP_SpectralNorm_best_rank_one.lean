-- Prove2me | Theorems.Thm_TensorNP_SpectralNorm_best_rank_one
-- name    : TensorNP.SpectralNorm.best_rank_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:59.144959+00:00
-- url     : https://prove2.me/theorems/8f9c16f1-39fa-4fa8-aa1d-167bd4837ec7
-- title:
--   §7 — the best rank-1 approximation of a tensor is governed by its spectral norm
-- statement:
--   Let $\mathcal A\in\mathbb R^{a\times b\times c}$ with $a,b,c\ge1$. Then:
--
--   1. $\displaystyle\max_{\|\mathbf u\|_2=\|\mathbf v\|_2=\|\mathbf w\|_2=1}\langle\mathcal A,\mathbf u\otimes\mathbf v\otimes\mathbf w\rangle=\|\mathcal A\|_{2,2,2}$, where $\langle\mathcal A,\mathbf u\otimes\mathbf v\otimes\mathbf w\rangle=\mathcal A(\mathbf u,\mathbf v,\mathbf w)$;
--   2. the minimum of $\|\mathcal A-\sigma\,\mathbf u\otimes\mathbf v\otimes\mathbf w\|_F^2$ over $\sigma\ge0$ and unit vectors $\mathbf u,\mathbf v,\mathbf w$ exists and equals
--   $$
--   \|\mathcal A\|_F^2-\|\mathcal A\|_{2,2,2}^2 ;
--   $$
--   3. every minimizer has $\sigma=\|\mathcal A\|_{2,2,2}$.
--
--   This is the computation of §7 behind Theorem 1.13: a best rank-1 approximation $\mathbf x\otimes\mathbf y\otimes\mathbf z=\sigma\,\mathbf u\otimes\mathbf v\otimes\mathbf w$ determines the spectral norm as $\sigma=\|\mathbf x\|_2\|\mathbf y\|_2\|\mathbf z\|_2$, so computing best rank-1 approximations is at least as hard as computing spectral norms.
--
--   **Formalization Note** The first clause is `IsGreatest` of the attained values of the trilinear form on the product of unit spheres, with value the `sSup`-based `specNorm`; the second is `IsLeast` of the attained values of the squared Frobenius distance. The hypotheses $a,b,c\ge1$ make the unit spheres nonempty. The NP-hardness wording of Theorem 1.13 is not formalized.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:25, §7, display after (28) and the following paragraph (content of Theorem 1.13)

import Mathlib
import Definitions.Def_TensorNP_SpectralNorm_Tensor

namespace TensorNP.SpectralNorm

/-- **§7, best rank-1 approximation and the spectral norm** (p. 0:25). For a real tensor
`A ∈ ℝ^{a×b×c}` with `a, b, c ≥ 1`:
1. the maximum of `⟨A, u⊗v⊗w⟩ = A(u,v,w)` over `‖u‖₂ = ‖v‖₂ = ‖w‖₂ = 1` is `‖A‖_{2,2,2}`;
2. the minimum of `‖A − σ u⊗v⊗w‖_F²` over `σ ≥ 0` and unit `u, v, w` is
   `‖A‖_F² − ‖A‖_{2,2,2}²`;
3. every minimizer has `σ = ‖A‖_{2,2,2}`. -/
theorem best_rank_one {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A : Fin a → Fin b → Fin c → ℝ) :
    IsGreatest {t : ℝ | ∃ (u : Fin a → ℝ) (v : Fin b → ℝ) (w : Fin c → ℝ),
        l2norm u = 1 ∧ l2norm v = 1 ∧ l2norm w = 1 ∧ t = trilinear A u v w} (specNorm A) ∧
      IsLeast {t : ℝ | ∃ (σ : ℝ) (u : Fin a → ℝ) (v : Fin b → ℝ) (w : Fin c → ℝ),
          0 ≤ σ ∧ l2norm u = 1 ∧ l2norm v = 1 ∧ l2norm w = 1 ∧
          t = frobSq (fun i j k => A i j k - σ * outer3 u v w i j k)}
        (frobSq A - specNorm A ^ 2) ∧
      ∀ (σ : ℝ) (u : Fin a → ℝ) (v : Fin b → ℝ) (w : Fin c → ℝ),
        0 ≤ σ → l2norm u = 1 → l2norm v = 1 → l2norm w = 1 →
        frobSq (fun i j k => A i j k - σ * outer3 u v w i j k) = frobSq A - specNorm A ^ 2 →
        σ = specNorm A := by sorry

end TensorNP.SpectralNorm
