-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_theorem_10_sufficient
-- name    : SunNLSDP.Equiv.theorem_10_sufficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:53.583764+00:00
-- url     : https://prove2.me/theorems/3c6a33ad-a233-45fd-8952-4d4d9842eb35
-- title:
--   Theorem 10, pp. 14–15 — (45) is necessary and sufficient for quadratic growth (46) under Robinson's CQ
-- statement:
--   Let $K=\{0\}\times\mathcal S^p_+$ and $G=(h,g)$. Let $\bar x$ be feasible for (NLSDP) with $\mathcal M(\bar x)\neq\emptyset$, and suppose Robinson's CQ holds at $\bar x$. Then the condition
--
--   $$\sup_{\mu\in\mathcal M(\bar x)}\Big\{\langle d,J^2_{xx}L(\bar x,\mu)d\rangle-\sigma\big(\mu,T^2_K(G(\bar x),J_xG(\bar x)d)\big)\Big\}>0\qquad\forall d\in C(\bar x)\setminus\{0\}\qquad(45)$$
--
--   holds if and only if there are $c>0$ and a neighbourhood $\widehat N$ of $\bar x$ with
--
--   $$f(x)\ge f(\bar x)+c\|x-\bar x\|^2\qquad\forall x\in\widehat N\text{ such that }G(x)\in K.\qquad(46)$$
--
--   **Formalization Note.** "The supremum is $>0$" is stated as "some $\mu\in\mathcal M(\bar x)$ gives a value $>0$" in the extended reals, which is equivalent.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, pp. 14–15, Theorem 10 (45), (46) (from Bonnans and Shapiro [4])

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem theorem_10_sufficient {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X)
    (hfeas : P.feasible xbar) (hM : (P.multipliers xbar).Nonempty)
    (hCQ : P.RobinsonCQ xbar) :
    (∀ d ∈ P.criticalCone xbar, d ≠ 0 → ∃ μ ∈ P.multipliers xbar,
        (0 : EReal) < ((P.hessL xbar μ.1 μ.2 d : ℝ) : EReal) - P.sigmaTerm xbar μ d) ↔
      ∃ c > (0 : ℝ), ∃ N ∈ 𝓝 xbar, ∀ x ∈ N, P.feasible x →
        P.f x ≥ P.f xbar + c * ‖x - xbar‖ ^ 2 := by sorry
end SunNLSDP.Equiv
