-- Prove2me | Theorems.Thm_PELiquidity_Secondary_mu2_welldefined
-- name    : PELiquidity.Secondary.mu2_welldefined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:25.137076+00:00
-- url     : https://prove2.me/theorems/0e37aaaa-511d-47f3-b65c-99e74d9e620a
-- title:
--   Appendix C.6: the capital-call threshold lies inside the discount range
-- statement:
--   Write $g(D_L)=(1-\lambda)D_L/(1-\lambda D_L)$ for the capital call that binds the no-default constraint, and $\bar x=p/(p+q)$ for the upper endpoint of the undistorted call interval. Under Assumption 6, $g$ increases strictly on the possible discount range and
--   $$
--   g(1-\delta_H)<\bar x<g(1-\delta_L).
--   $$
--   Also $g(1-\delta)=\hat x(\lambda,\delta)$. Thus the crossing used to define the middle capital-share threshold occurs within the discount range.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 52, Appendix C.6, paragraph defining μ_H,2

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Secondary

theorem mu2_welldefined (P : PELiquidity.Primary.Params) :
    let g : ℝ → ℝ := fun D => (1 - P.lam) * D / (1 - P.lam * D)
    StrictMonoOn g (Set.Icc (1 - P.δH) (1 - P.δL)) ∧
    g (1 - P.δH) < PELiquidity.Primary.xBar P.p P.q ∧
    PELiquidity.Primary.xBar P.p P.q < g (1 - P.δL) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 → g (1 - δ) = PELiquidity.Primary.xHat P.lam δ) := by sorry

end PELiquidity.Secondary
