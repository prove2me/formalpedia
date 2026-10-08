-- Prove2me | Theorems.Thm_SmartPTO_Fisher_theorem1_fisher_consistency
-- name    : SmartPTO.Fisher.theorem1_fisher_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:03:20.258162+00:00
-- url     : https://prove2.me/theorems/532d866c-8a7f-4ce6-8ff2-61d6f5028005
-- title:
--   Theorem 1 — Fisher consistency of SPO+ under Assumption 1
-- statement:
--   Let $x$ be a feature in a measurable space $X$, with probability law $\nu$, and let $\kappa_x$ be the conditional probability law of a cost vector $c\in\mathbb R^d$ given $x$. Write $D=\nu\otimes\kappa$ for their joint law and $m(x)=\mathbb E_{\kappa_x}[c]$. Let $S\subseteq\mathbb R^d$ be nonempty, compact, and convex, and let $w^*$ be any oracle returning an optimal decision for each cost.
--
--   Suppose costs are integrable jointly and under each conditional law. Assume that $W^*(m(x))$ is a singleton for $\nu$-almost every $x$, that every $\kappa_x$ is centrally symmetric about $m(x)$ and continuous on all of $\mathbb R^d$, and that $S$ has nonempty interior. If a measurable predictor $f:X\to\mathbb R^d$ minimizes the SPO+ population risk among all measurable predictors, then
--
--   $$f(x)=m(x)\quad\text{for }\nu\text{-almost every }x,\qquad R_{\mathrm{SPO}}(f)\le R_{\mathrm{SPO}}(g)\quad\text{for every measurable }g:X\to\mathbb R^d.$$
--
--   This is the Fisher-consistency conclusion of Theorem 1: every minimizer of the surrogate population risk also minimizes the true decision risk.
--
--   **Formalization Note** “Continuous on all” is pinned to absolute continuity plus full support; absolute continuity alone does not support the printed uniqueness claim. Risks are extended nonnegative integrals, preserving infinite values. The joint law is represented by a marginal and Markov kernel, and cost integrability makes the conditional and joint means finite. The oracle is arbitrary; the SPO risk uses the unambiguous loss of Definition 2.
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, p. 21, Theorem 1 and Assumption 1; (11)–(12) p. 20; proof App. B.5 p. 40

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model
import Definitions.Def_SmartPTO_Fisher_Setting

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- Theorem 1, p. 21, under Assumption 1: Fisher consistency of SPO+. -/
theorem theorem1_fisher_consistency {d : ℕ} {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (κ : Kernel X (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel κ]
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hSne : S.Nonempty) (hScpt : IsCompact S) (hScvx : Convex ℝ S)
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hw : SPOBounds.Natarajan.IsOracle S wstar)
    (hCondInt : ∀ x, Integrable id (κ x))
    (hJointInt : Integrable (fun p : X × EuclideanSpace ℝ (Fin d) => p.2) (ν ⊗ₘ κ))
    (hSingle : ∀ᵐ x ∂ν, ∃ w, Wstar S (∫ c, c ∂(κ x)) = {w})
    (hSymm : ∀ x, CentrallySymmetric (κ x))
    (hCont : ∀ x, ContinuousOnAll (κ x))
    (hSinner : (interior S).Nonempty)
    (f : X → EuclideanSpace ℝ (Fin d)) (hf : Measurable f)
    (hMin : ∀ g : X → EuclideanSpace ℝ (Fin d), Measurable g →
      spoPlusRiskJoint S wstar (ν ⊗ₘ κ) f ≤ spoPlusRiskJoint S wstar (ν ⊗ₘ κ) g) :
    (f =ᵐ[ν] fun x => ∫ c, c ∂(κ x)) ∧
      ∀ g : X → EuclideanSpace ℝ (Fin d), Measurable g →
        spoRiskJoint S (ν ⊗ₘ κ) f ≤ spoRiskJoint S (ν ⊗ₘ κ) g := by sorry

end SmartPTO.Fisher
