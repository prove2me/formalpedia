-- Prove2me | Theorems.Thm_PertComp_proposition_2_9_ii
-- name    : PertComp.proposition_2_9_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:00.719818+00:00
-- url     : https://prove2.me/theorems/cc4acd83-b3fb-4334-858e-c48736eaabd5
-- title:
--   Proposition 2.9(ii): $\varphi\circ f\in\Gamma_0(X)$
-- statement:
--   Let $X$ be a reflexive real Banach space, let $\varphi\in\Gamma_0(\mathbb R)$ be a nonconstant increasing function, and let $f\in\Gamma_0(X)$ be such that $(\operatorname{dom}\varphi)\cap f(\operatorname{dom} f)\ne\varnothing$. Then the composition (1.1),
--   $$(\varphi\circ f)(x)=\begin{cases}\varphi(f(x)), & f(x)\in\operatorname{dom}\varphi;\\ +\infty, & \text{otherwise},\end{cases}$$
--   belongs to $\Gamma_0(X)$.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 2.9(ii), p.7

import Mathlib
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PerspEpi_postComp

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Proposition 2.9(ii)**, p.7: let `X` be a
reflexive real Banach space, `φ ∈ Γ₀(ℝ)` a nonconstant increasing function and `f ∈ Γ₀(X)` with
`(dom φ) ∩ f(dom f) ≠ ∅`. Then `φ ∘ f ∈ Γ₀(X)`, where `φ ∘ f` is (1.1).

**Formalization Note.** `φ ∘ f` of (1.1) is the published `PerspEpi.postComp φ f`
(`φ(f(x))` on `dom f`, `+∞` off it); when `x ∈ dom f` but `f(x) ∉ dom φ` its value `φ(f(x))` is
already `+∞`, as (1.1) prescribes.
"Increasing" is `Monotone φ`; "nonconstant" is `∃ a b, φ a ≠ φ b`;
`(dom φ) ∩ f(dom f) ≠ ∅` is `∃ x, f x ≠ ⊤ ∧ φ (f x) ≠ ⊤`. -/
theorem proposition_2_9_ii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (φ : ℝ → EReal) (hφ : TensorAHPE.IsProperClosedConvex φ)
    (hnc : ∃ a b : ℝ, φ a ≠ φ b)
    (hmono : Monotone φ) (f : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f)
    (hdom : ∃ x : X, f x ≠ ⊤ ∧ φ (f x).toReal ≠ ⊤) :
    TensorAHPE.IsProperClosedConvex (PerspEpi.postComp φ f) := by sorry

end PertComp
