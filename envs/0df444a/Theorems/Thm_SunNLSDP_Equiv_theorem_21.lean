-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_theorem_21
-- name    : SunNLSDP.Equiv.theorem_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:53.914733+00:00
-- url     : https://prove2.me/theorems/444c548d-aea4-4212-a205-22d4bf4d379b
-- title:
--   Theorem 21, pp. 22–23 — at a local minimizer of (NLSDP) with Robinson's CQ: SSOSC + nondegeneracy ⇔ ∂F nonsingular ⇔ strong regularity ⇔ …
-- statement:
--   Let $\bar x$ be a locally optimal solution of the nonlinear semidefinite program
--
--   $$\min f(x)\quad\text{s.t.}\quad h(x)=0,\ g(x)\in\mathcal S^p_+,$$
--
--   with $f,h,g$ twice continuously differentiable, suppose Robinson's CQ holds at $\bar x$, and let $(\bar\zeta,\bar\Gamma)\in\Re^m\times\mathcal S^p$ be such that $(\bar x,\bar\zeta,\bar\Gamma)$ is a KKT point. Let $F$ be the KKT map (51) and $\Phi:=F'(\bar x,\bar\zeta,\bar\Gamma;\cdot)$. Then the following are equivalent:
--
--   1. (a) the strong second order sufficient condition (47) holds at $\bar x$ and $\bar x$ is constraint nondegenerate;
--   2. (b) every element of $\partial F(\bar x,\bar\zeta,\bar\Gamma)$ is nonsingular;
--   3. (c) $(\bar x,\bar\zeta,\bar\Gamma)$ is a strongly regular solution of the generalized equation (52);
--   4. (d) the uniform second order growth condition holds at $\bar x$ and $\bar x$ is constraint nondegenerate;
--   5. (e) $\bar x$ is strongly stable and constraint nondegenerate;
--   6. (f) $F$ is a locally Lipschitz homeomorphism near $(\bar x,\bar\zeta,\bar\Gamma)$;
--   7. (h) $\Phi$ is a globally Lipschitz homeomorphism;
--   8. (j) every element of $\partial\Phi(0)$ is nonsingular.
--
--   This is the main result of the paper: it extends to semidefinite programming the classical equivalence, for nonlinear programming, between Robinson's strong second order sufficient condition with linear independence of active gradients and strong regularity of the KKT point.
--
--   **Formalization Note.** Items (g) and (i) of the paper, which involve the topological degree index $\mathrm{ind}(\cdot,\cdot)$, are omitted: Brouwer degree is not available in Mathlib. Robinson's CQ (41) is read as the coupled system (7) in $\Re^m\times\mathcal S^p$. Local optimality is local minimality of $f$ on the feasible set, together with feasibility of $\bar x$. Parameterizations in (d), (e) range over Banach spaces in the universe of $X$. "Nonsingular" means bijective.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, pp. 22–23, Theorem 21 (items (a)–(f), (h), (j); (g), (i) omitted)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local
universe v

namespace SunNLSDP.Equiv
theorem theorem_21 {X : Type v} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (ζbar : EuclideanSpace ℝ (Fin m)) (Γbar : SymMat n)
    (hfeas : P.feasible xbar) (hloc : IsLocalMinOn P.f {x | P.feasible x} xbar)
    (hCQ : P.RobinsonCQ xbar) (hKKT : (ζbar, Γbar) ∈ P.multipliers xbar) :
    List.TFAE
      [ P.SSOSC xbar ∧ P.Nondegenerate xbar,
        ∀ W ∈ clarkeJac (kktMap P) (kktPt xbar ζbar Γbar), Function.Bijective W,
        StronglyRegular (geMap P) (geSet X m n) (kktPt xbar ζbar Γbar),
        UniformGrowth P xbar ∧ P.Nondegenerate xbar,
        StronglyStable P xbar ∧ P.Nondegenerate xbar,
        LocLipHomeo (kktMap P) (kktPt xbar ζbar Γbar),
        GlobLipHomeo (kktDirDeriv P (kktPt xbar ζbar Γbar)),
        ∀ W ∈ clarkeJac (kktDirDeriv P (kktPt xbar ζbar Γbar)) 0, Function.Bijective W ] := by sorry
end SunNLSDP.Equiv
