-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_theorem_10_necessary
-- name    : SunNLSDP.Equiv.theorem_10_necessary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:41.032594+00:00
-- url     : https://prove2.me/theorems/bb9b0014-e6b0-441e-9714-f0ad459a0450
-- title:
--   Theorem 10, p. 14 — second order necessary condition (44) at a local minimizer under Robinson's CQ
-- statement:
--   Let $K=\{0\}\times\mathcal S^p_+\subset\Re^m\times\mathcal S^p$ and $G=(h,g)$. Suppose $\bar x$ is a locally optimal solution of (NLSDP) and Robinson's CQ holds at $\bar x$. Then
--
--   $$\sup_{\mu\in\mathcal M(\bar x)}\Big\{\langle d,J^2_{xx}L(\bar x,\mu)d\rangle-\sigma\big(\mu,T^2_K(G(\bar x),J_xG(\bar x)d)\big)\Big\}\ \ge\ 0\qquad\forall d\in C(\bar x).\qquad(44)$$
--
--   Here $T^2_K$ is the outer second order tangent set (30) and $\sigma$ the support function, so the bracket may be $+\infty$ (when the tangent set is empty).
--
--   **Formalization Note.** The supremum and the support function take values in the extended reals $[-\infty,+\infty]$; $\langle d,J^2_{xx}Ld\rangle$ is the second Fréchet derivative of $x\mapsto L(x,\mu)$ evaluated at $(d,d)$.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 14, Theorem 10 (44) (from Bonnans and Shapiro [4])

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem theorem_10_necessary {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X)
    (hfeas : P.feasible xbar) (hloc : IsLocalMinOn P.f {x | P.feasible x} xbar)
    (hCQ : P.RobinsonCQ xbar) :
    ∀ d ∈ P.criticalCone xbar,
      (0 : EReal) ≤ ⨆ μ ∈ P.multipliers xbar,
        (((P.hessL xbar μ.1 μ.2 d : ℝ) : EReal) - P.sigmaTerm xbar μ d) := by sorry
end SunNLSDP.Equiv
