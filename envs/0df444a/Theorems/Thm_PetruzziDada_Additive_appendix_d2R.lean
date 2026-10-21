-- Prove2me | Theorems.Thm_PetruzziDada_Additive_appendix_d2R
-- name    : PetruzziDada.Additive.appendix_d2R
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:12.763256+00:00
-- url     : https://prove2.me/theorems/cff08b26-d437-4134-b343-ae319d8d59a5
-- title:
--   Appendix, proof of Theorem 1 (p. 193) — d²R/dz² at a critical point of R
-- statement:
--   In the additive-demand price-setting newsvendor, let $R(z) = dE[\Pi(z,p(z))]/dz$ and let $r(z) = f(z)/[1-F(z)]$ be the hazard rate. Assume the density $f$ is differentiable on $(A,B)$. Let $z \in (A,B)$ with $f(z) > 0$ be a critical point of $R$, i.e. $dR(z)/dz = 0$. Then $dR/dz$ is differentiable at $z$, and
--   $$\left.\frac{d^2R(z)}{dz^2}\right|_{dR(z)/dz=0} = -\frac{f(z)[1-F(z)]}{2b\,r(z)^2}\Big\{2r(z)^2 + \frac{dr(z)}{dz}\Big\}.$$
--
--   This is the display of the paper's proof of Theorem 1 on p. 193. It shows that under the condition $2r(z)^2 + dr(z)/dz > 0$ every interior critical point of $R$ is a strict local maximum of $R$.
--
--   **Formalization Note** Differentiability of $f$ on $(A,B)$ and $f(z) > 0$ are added: the paper differentiates $f$ and divides by $r(z)$ without stating these. The derivative $dr/dz$ is Mathlib's `deriv` of the hazard rate, which is the genuine derivative here because $f$ and $F$ are differentiable at $z$ and $F(z) < 1$.
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, pp. 192–193, Appendix, proof of Theorem 1, d²R(z)/dz² at dR(z)/dz = 0

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Appendix, proof of Theorem 1, pp. 192–193: at a critical point `z ∈ (A, B)` of `R`
(with `f` differentiable on `(A, B)` and `f(z) > 0`), `R` is twice differentiable and
`d²R(z)/dz² = -(f(z)[1 - F(z)]/(2b r(z)²)){2r(z)² + dr(z)/dz}`. -/
theorem appendix_d2R (M : Model) (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B))
    (z : ℝ) (hz : z ∈ Set.Ioo M.A M.B) (hfz : 0 < M.f z) (hcrit : deriv M.R z = 0) :
    HasDerivAt (deriv M.R)
      (-(M.f z * (1 - M.F z) / (2 * M.b * M.hazard z ^ 2)) *
        (2 * M.hazard z ^ 2 + deriv M.hazard z)) z := by sorry
end PetruzziDada.Additive
