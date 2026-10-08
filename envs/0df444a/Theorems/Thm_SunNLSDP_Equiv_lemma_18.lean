-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_lemma_18
-- name    : SunNLSDP.Equiv.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:19.165187+00:00
-- url     : https://prove2.me/theorems/003bdc9e-9127-4ba6-b82a-d87a544fd1b3
-- title:
--   Lemma 18, p. 20 — uniform growth for the canonical parameterization ⇒ SSOSC (47)
-- statement:
--   Let $\bar x$ be a stationary point of (NLSDP) at which Robinson's CQ holds. If the uniform second order growth condition (62) holds at $\bar x$ with respect to the canonical parameterization
--
--   $$(f(x)-\langle u_1,x\rangle,\ G(x)+u_2),\qquad u=(u_1,u_2)\in X\times(\Re^m\times\mathcal S^p),\ \bar u=0,$$
--
--   then the strong second order sufficient condition (47) holds at $\bar x$.
--
--   This is the step (d) $\Rightarrow$ (a) of Theorem 21 on the optimization side.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 20, Lemma 18

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem lemma_18 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (hstat : P.stationary xbar) (hCQ : P.RobinsonCQ xbar)
    (hUG : UniformGrowthWrt (canonicalParam P) xbar) :
    P.SSOSC xbar := by sorry
end SunNLSDP.Equiv
