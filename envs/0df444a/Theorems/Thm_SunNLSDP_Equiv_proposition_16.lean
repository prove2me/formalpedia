-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_proposition_16
-- name    : SunNLSDP.Equiv.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:39.622122+00:00
-- url     : https://prove2.me/theorems/2565c5a1-cdc4-4037-8fc1-f2efb047c8b3
-- title:
--   Proposition 16, pp. 17–18 — at a KKT point: SSOSC + nondegeneracy ⇒ ∂F nonsingular ⇒ strong regularity
-- statement:
--   Let $\bar x$ be feasible for (NLSDP) and $(\bar\zeta,\bar\Gamma)\in\mathcal M(\bar x)$, i.e. $(\bar x,\bar\zeta,\bar\Gamma)$ is a KKT point. Consider:
--
--   1. (a) the strong second order sufficient condition (47) holds at $\bar x$ and $\bar x$ is constraint nondegenerate;
--   2. (b) every element of Clarke's generalized Jacobian $\partial F(\bar x,\bar\zeta,\bar\Gamma)$ is nonsingular;
--   3. (c) $(\bar x,\bar\zeta,\bar\Gamma)$ is a strongly regular solution of the generalized equation (52).
--
--   Then
--
--   $$\text{(a)}\Longrightarrow\text{(b)}\Longrightarrow\text{(c)}.$$
--
--   Here $F(x,\zeta,\Gamma)=(\nabla_xL(x,\zeta,\Gamma),\,-h(x),\,-g(x)+\Pi_{\mathcal S^p_+}(g(x)+\Gamma))$ is the KKT map (51). No local optimality and no constraint qualification is assumed.
--
--   **Formalization Note.** "Nonsingular" means that the linear map $Z\to Z$ is bijective, with $Z=X\times\Re^m\times\mathcal S^p$.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, pp. 17–18, Proposition 16

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem proposition_16 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (ζbar : EuclideanSpace ℝ (Fin m)) (Γbar : SymMat n)
    (hfeas : P.feasible xbar) (hKKT : (ζbar, Γbar) ∈ P.multipliers xbar) :
    ((P.SSOSC xbar ∧ P.Nondegenerate xbar) →
        ∀ W ∈ clarkeJac (kktMap P) (kktPt xbar ζbar Γbar), Function.Bijective W) ∧
      ((∀ W ∈ clarkeJac (kktMap P) (kktPt xbar ζbar Γbar), Function.Bijective W) →
        StronglyRegular (geMap P) (geSet X m n) (kktPt xbar ζbar Γbar)) := by sorry
end SunNLSDP.Equiv
