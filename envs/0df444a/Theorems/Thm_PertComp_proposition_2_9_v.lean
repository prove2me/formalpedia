-- Prove2me | Theorems.Thm_PertComp_proposition_2_9_v
-- name    : PertComp.proposition_2_9_v
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:28.343339+00:00
-- url     : https://prove2.me/theorems/9069a87b-bb5e-451a-8c79-28cb48b74ee9
-- title:
--   Proposition 2.9(v): chain rule $\partial(\varphi\circ f)(x)=\bigcup_{\xi^*\in\partial\varphi(f(x))}\partial(\xi^*\odot f)(x)$
-- statement:
--   Let $X$ be a reflexive real Banach space, let $\varphi\in\Gamma_0(\mathbb R)$ be a nonconstant increasing function, and let $f\in\Gamma_0(X)$ be such that $(\operatorname{dom}\varphi)\cap f(\operatorname{dom} f)\ne\varnothing$. Suppose that there exists $z\in\operatorname{dom} f$ such that $f(z)\in\operatorname{int}\operatorname{dom}\varphi$, and let $x\in\operatorname{dom} f$. Then
--   $$\partial(\varphi\circ f)(x)=\bigcup_{\xi^*\in\partial\varphi(f(x))}\partial(\xi^*\odot f)(x).$$
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: φ*, ∂φ and ∂φ* with ℝ* identified with ℝ; the real dual variable ξ* → PWDB.conj φ (the conjugate on the inner-product space ℝ, ⟨t, s⟩ = t s), subdiffR, and realDual ξ* = (ξ ↦ ξ ξ*) as the element of StrongDual ℝ ℝ; reason: canonical isomorphism ℝ ≅ ℝ*; same values
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 2.9(v), (2.15), p.8 (preamble p.7)

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PerspEpi_postComp
import Definitions.Def_PertComp_subdiffR
import Definitions.Def_PertComp_odot

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Proposition 2.9(v)**, (2.15), p.8: let `X` be a
reflexive real Banach space, `φ ∈ Γ₀(ℝ)` a nonconstant increasing function and `f ∈ Γ₀(X)` with
`(dom φ) ∩ f(dom f) ≠ ∅`. Suppose that there exists `z ∈ dom f` with `f(z) ∈ int dom φ`, and let
`x ∈ dom f`. Then `∂(φ ∘ f)(x) = ⋃_{ξ* ∈ ∂φ(f(x))} ∂(ξ* ⊙ f)(x)`.

**Formalization Note.** `φ ∘ f` of (1.1) is the published `PerspEpi.postComp φ f`
(`φ(f(x))` on `dom f`, `+∞` off it); when `x ∈ dom f` but `f(x) ∉ dom φ` its value `φ(f(x))` is
already `+∞`, as (1.1) prescribes.
`∂φ(f(x))` is the real subdifferential `subdiffR φ` at the real number
`f(x)`; its elements are nonnegative (φ increasing), so `ξ* ⊙ f` is used only at `ξ* ≥ 0`. -/
theorem proposition_2_9_v {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (φ : ℝ → EReal) (hφ : TensorAHPE.IsProperClosedConvex φ)
    (hnc : ∃ a b : ℝ, φ a ≠ φ b)
    (hmono : Monotone φ) (f : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f)
    (hdom : ∃ x : X, f x ≠ ⊤ ∧ φ (f x).toReal ≠ ⊤)
    (hz : ∃ z : X, f z ≠ ⊤ ∧ (f z).toReal ∈ interior {t : ℝ | φ t ≠ ⊤})
    (x : X) (hx : f x ≠ ⊤) :
    RockafellarMaxMono.Shared.subdiff (PerspEpi.postComp φ f) x =
      ⋃ ξ' ∈ subdiffR φ (f x).toReal, RockafellarMaxMono.Shared.subdiff (odot ξ' f) x := by sorry

end PertComp
