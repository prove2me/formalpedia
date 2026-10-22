-- Prove2me | Theorems.Thm_TwoSidedExp_DemandLimit_control_choice_identity
-- name    : TwoSidedExp.DemandLimit.control_choice_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:34.711416+00:00
-- url     : https://prove2.me/theorems/94332516-d78f-4ab6-b195-74f76d950c88
-- title:
--   Proof of Theorem 3, p. A7 — a control customer's choice probability for treated listings when all are treated equals that for control listings when none are
-- statement:
--   For every customer type $\gamma$ and listing type $\theta$,
--   $$p_{\gamma,0}(\theta,1\mid\rho(1))=p_{\gamma,0}(\theta,0\mid\rho(0)),$$
--   where $p_{\gamma,i}(\theta,j\mid\cdot)$ is the choice probability of the TSR experimental system, $\rho(1)$ is the mass vector with every listing treated ($\rho(\theta,1)=\rho(\theta)$, $\rho(\theta,0)=0$) and $\rho(0)$ the one with every listing in control.
--
--   A control customer sees the same parameters for treated and control listings, and both mass vectors put the whole mass on one condition; this is the observation that makes the CR limit equal the GTE limit.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, Proof of Theorem 3, p. A7

import Mathlib
import Definitions.Def_TwoSidedExp_DemandLimit_Setting

open Filter Topology MeasureTheory

namespace TwoSidedExp.DemandLimit

/-- Proof of Theorem 3, p. A7: the choice probability of a control customer for a treatment listing
at `ρ(1)` equals that of a control customer for a control listing at `ρ(0)`:
`p_{γ,0}(θ,1|ρ(1)) = p_{γ,0}(θ,0|ρ(0))`. -/
theorem control_choice_identity {Γ Θ : Type} [Fintype Γ] [Fintype Θ] (M : Model Γ Θ)
    (hM : M.Standing) (γ : Γ) (θ : Θ) :
    M.pE (γ, 0) (θ, 1) (M.rhoL 1) = M.pE (γ, 0) (θ, 0) (M.rhoL 0) := by sorry

end TwoSidedExp.DemandLimit
