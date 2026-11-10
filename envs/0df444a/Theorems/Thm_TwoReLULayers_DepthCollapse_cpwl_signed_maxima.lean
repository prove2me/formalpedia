-- Prove2me | Theorems.Thm_TwoReLULayers_DepthCollapse_cpwl_signed_maxima
-- name    : TwoReLULayers.DepthCollapse.cpwl_signed_maxima
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T10:35:56.49343+00:00
-- url     : https://prove2.me/theorems/d77cc1bc-ca67-4db4-ba33-77ffe2c954b2
-- title:
--   Equation (2) — coefficient-preserving geometric CPWL reduction
-- statement:
--   Let $n\ge1$, let $R\subseteq\mathbb R$ be a subfield, and let $f\in\operatorname{CPWL}(R,n)$ in the independent geometric sense. There are finitely many signs $\sigma_i\in\{-1,1\}$ and affine maps $A_i:E_n\to E_{n+1}$ with all coefficients in $R$ such that
--   $$f(x)=\sum_i\sigma_i\operatorname{MAX}_{n+1}(A_i(x))\quad\text{for every }x\in E_n.$$
--   This is the full coefficient-aware bridge from geometric CPWL to MAX. The existing real lattice-based Wang–Sun result does not supply the geometric or field-preserving part automatically.
--
--   Differences from the source:
--   - encoding: real inputs, field R containing the rationals, finite polyhedral partition and two hidden layers → Subfield ℝ, EuclideanSpace ℝ (Fin n), finite closed polyhedral cover and three affine-map evaluator; reason: every real subfield contains ℚ; common hyperplane refinement identifies the cover with a partition; widths remain arbitrary finite naturals
-- source:
--   Kilian Rueß, Florestan Brunck, Christoph Hertrich, Jack Stade, Amir Yehudayoff, Two ReLU layers is all you need, STOC 2027 submission #980 (October 2026), p. 2, Section 1, Eq. (2)

import Definitions.Def_TwoReLULayers_DepthCollapse_Construction

namespace TwoReLULayers.DepthCollapse

theorem cpwl_signed_maxima {n : ℕ} (hn : 1 ≤ n) (R : Subfield ℝ)
    (f : E n → ℝ) (hf : f ∈ CPWL R n) :
    ∃ k : ℕ, ∃ σ : Fin k → ℝ, ∃ A : Fin k → AffineR R n (n + 1),
      (∀ i, IsSign (σ i)) ∧ ∀ x : E n,
        f x = ∑ i, σ i * maxCoord (affineEval (A i) x) := by sorry

end TwoReLULayers.DepthCollapse
