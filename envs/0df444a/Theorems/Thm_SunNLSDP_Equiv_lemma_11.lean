-- Prove2me | Theorems.Thm_SunNLSDP_Equiv_lemma_11
-- name    : SunNLSDP.Equiv.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:39:20.173265+00:00
-- url     : https://prove2.me/theorems/19ee96df-6d83-4d51-b601-750b3442b904
-- title:
--   Lemma 11, p. 15 — Υ_{g(x̄)}(Γ, J_xg(x̄)d) = σ(Γ, T²_{S^p_+}(g(x̄), J_xg(x̄)d)) on C(x̄)
-- statement:
--   Let $\bar x$ be feasible for (NLSDP) with $\mathcal M(\bar x)\neq\emptyset$. Then for every $(\zeta,\Gamma)\in\mathcal M(\bar x)$,
--
--   $$\Upsilon_{g(\bar x)}\big(\Gamma,J_xg(\bar x)d\big)=\sigma\big(\Gamma,T^2_{\mathcal S^p_+}(g(\bar x),J_xg(\bar x)d)\big)\qquad\forall d\in C(\bar x).$$
--
--   The lemma identifies the sigma term of the classical second order conditions with the explicit quadratic function $\Upsilon$, which makes sense for all $d$ and is used to define the strong second order sufficient condition (47).
--
--   **Formalization Note.** The equality is in the extended reals; the left side is a real number.
-- source:
--   Sun, The strong second order sufficient condition and constraint nondegeneracy in nonlinear semidefinite programming and their implications, preprint dated May 15, 2005, p. 15, Lemma 11 (due to Shapiro [35] and Bonnans–Shapiro [4])

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_Local_dirDeriv
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_SunNLSDP_Equiv_Setting

open scoped RealInnerProductSpace Topology
open Filter NonsmoothNewton.Shared NonsmoothNewton.Local

namespace SunNLSDP.Equiv
theorem lemma_11 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {m : ℕ} {n : Type} [Fintype n] [DecidableEq n]
    (P : NLSDP X m n) (xbar : X) (hfeas : P.feasible xbar)
    (hM : (P.multipliers xbar).Nonempty)
    (ζ : EuclideanSpace ℝ (Fin m)) (Γ : SymMat n) (hμ : (ζ, Γ) ∈ P.multipliers xbar) :
    ∀ d ∈ P.criticalCone xbar,
      ((upsilon (P.g xbar) Γ (fderiv ℝ P.g xbar d) : ℝ) : EReal) =
        supportFn Γ (secondOrderTangentSet (psdCone n) (P.g xbar) (fderiv ℝ P.g xbar d)) := by sorry
end SunNLSDP.Equiv
