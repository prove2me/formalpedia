-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_proposition_8
-- name    : SunNLSDP.Equiv.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:37.953762+00:00
-- url     : https://prove2.me/theorems/3c8312a0-c06c-452c-a822-339f350ed5f3
-- title:
--   Proposition 8, p. 13 — under the strict CQ (42), M(x̄) = {(ζ̄, Γ̄)} and aff(C(x̄)) = app(ζ̄, Γ̄)
-- statement:
--   Let $\bar x$ be feasible for (NLSDP) and $(\bar\zeta,\bar\Gamma)\in\mathcal M(\bar x)$. Suppose the strict constraint qualification (42) holds:
--
--   $$\begin{cases}J_xh(\bar x)X=\Re^m,\\ J_xg(\bar x)X+T_{\mathcal S^p_+}(g(\bar x))\cap\bar\Gamma^\perp=\mathcal S^p.\end{cases}$$
--
--   Then $\mathcal M(\bar x)=\{(\bar\zeta,\bar\Gamma)\}$ and $\mathrm{aff}(C(\bar x))=\mathrm{app}(\bar\zeta,\bar\Gamma)$, where $C(\bar x)$ is the critical cone (31) and $\mathrm{app}(\bar\zeta,\bar\Gamma)=\{d:J_xh(\bar x)d=0,\ J_xg(\bar x)d\in\mathrm{aff}(C(g(\bar x)+\bar\Gamma;\mathcal S^p_+))\}$ (38).
--
--   **Formalization Note.** (42) is read as one coupled system: for every $(a,B)\in\Re^m\times\mathcal S^p$ there is one $d\in X$ with $J_xh(\bar x)d=a$ and $B-J_xg(\bar x)d\in T_{\mathcal S^p_+}(g(\bar x))\cap\bar\Gamma^\perp$. This is the reading used in the proof ((43)); read as two separate equations it would be strictly weaker.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 13, Proposition 8 (42)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem proposition_8 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (ζbar : EuclideanSpace ℝ (Fin m)) (Γbar : SymMat n)
    (hfeas : P.feasible xbar) (hKKT : (ζbar, Γbar) ∈ P.multipliers xbar)
    (hstrict : P.StrictCQ xbar Γbar) :
    P.multipliers xbar = {(ζbar, Γbar)} ∧
      (affineSpan ℝ (P.criticalCone xbar) : Set X) = P.app xbar ζbar Γbar := by sorry
end SunNLSDP.Equiv
