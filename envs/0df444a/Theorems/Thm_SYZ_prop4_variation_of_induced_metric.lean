-- Prove2me | Theorems.Thm_SYZ_prop4_variation_of_induced_metric
-- name    : SYZ.prop4_variation_of_induced_metric
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T03:59:36.125256+00:00
-- url     : https://prove2.me/theorems/467e10f4-d69b-46e7-8f2e-fd052fd420cb
-- title:
--   SYZ Proposition 4: $\frac{d}{dt} g_{ij} = 2\,h_{ijk} w^{k}$
-- statement:
--   **Proposition 4 of Strominger–Yau–Zaslow.** Let $f_t$ be a smooth one-parameter family of Lagrangian maps $\mathbb R^n \to \mathbb C^n$ moving by the flow
--   $$\dot f_t \;=\; J\,f_{t*}w \;=\; \sum_k i\,w^k\,\partial_k f_t,$$
--   that is, with velocity the image under the ambient complex structure $J$ of the tangent vector field $w$ pushed forward to the brane — the flow (3.1) of the paper. Then the induced metric varies by twice the second fundamental form contracted with $w$:
--   $$\frac{d}{dt}\,g_{ij} \;=\; 2\,\sum_k h_{ijk}\,w^{k},\qquad h_{ijk} \;=\; \omega\!\left(\partial_i\partial_j f,\ \partial_k f\right).$$
--
--   The right-hand side is twice $(h^{w})_{ij}$, the second fundamental form in the direction of the normal vector $J\cdot w$. The Lagrangian hypothesis is what makes the terms involving the derivatives of $w$ drop out, and is also what makes $h$ a symmetric $3$-tensor.
-- source:
--   A. Strominger, S.-T. Yau, E. Zaslow, "Mirror symmetry is T-duality", Nuclear Physics B 479 (1996) 243-259, doi:10.1016/0550-3213(96)00434-8, arXiv:hep-th/9606040, p. 252, Proposition 4 (flow equation (3.1), p. 251)

import Definitions.Def_syz_flat_model

namespace SYZ

theorem prop4_variation_of_induced_metric {n : ℕ} (F : ℝ → Dom n → Amb n)
    (w : ℝ → Dom n → Fin n → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Dom n => F p.1 p.2))
    (hLag : ∀ s y, IsLagrangianAt (F s) y)
    (hflow : ∀ s y, deriv (fun r => F r y) s
      = ∑ k, (Complex.I * (w s y k : ℂ)) • D (F s) k y)
    (t : ℝ) (x : Dom n) (i j : Fin n) :
    deriv (fun s => gInd (F s) x i j) t
      = 2 * ∑ k, hTen (F t) i j k x * w t x k := by sorry

end SYZ
