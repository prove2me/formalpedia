-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_proposition_7
-- name    : SunNLSDP.Equiv.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:37.741926+00:00
-- url     : https://prove2.me/theorems/d91b0601-0c47-45de-94a7-3ba529ec8671
-- title:
--   Proposition 7, p. 10 — for V ∈ ∂Π_{S^p_+}(B + Γ) and ΔB = V(ΔB + ΔΓ): ⟨ΔB, ΔΓ⟩ ≥ −Υ_B(Γ, ΔB)
-- statement:
--   Let $B\in\mathcal S^p_+$ and $\Gamma\in N_{\mathcal S^p_+}(B)$ (so $\Gamma\preceq0$ and $\langle\Gamma,B\rangle=0$). Then for any $V$ in Clarke's generalized Jacobian $\partial\Pi_{\mathcal S^p_+}(B+\Gamma)$ and any $\Delta B,\Delta\Gamma\in\mathcal S^p$ with $\Delta B=V(\Delta B+\Delta\Gamma)$,
--
--   $$\langle\Delta B,\Delta\Gamma\rangle\ \ge\ -\Upsilon_B(\Gamma,\Delta B),\qquad \Upsilon_B(\Gamma,A)=2\langle\Gamma,AB^\dagger A\rangle .\qquad(22)$$
--
--   This inequality is where the curvature term $\Upsilon$ of the strong second order sufficient condition enters the nonsingularity argument for Clarke's Jacobian of the KKT map.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 10, Proposition 7 (22)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem proposition_7 {n : Type} [Fintype n] [DecidableEq n]
    (B Γ : SymMat n) (hB : B ∈ psdCone n)
    (hΓ : Γ ∈ RobinsonSR.Reduction.normalCone (psdCone n) B)
    (V : SymMat n →L[ℝ] SymMat n) (hV : V ∈ clarkeJac (metricProj (psdCone n)) (B + Γ))
    (ΔB ΔΓ : SymMat n) (hΔ : ΔB = V (ΔB + ΔΓ)) :
    ⟪ΔB, ΔΓ⟫ ≥ -upsilon B Γ ΔB := by sorry
end SunNLSDP.Equiv
