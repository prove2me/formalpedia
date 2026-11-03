-- Prove2me | Theorems.Thm_PertComp_proposition_3_1_i
-- name    : PertComp.proposition_3_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:08.665545+00:00
-- url     : https://prove2.me/theorems/dc3119cb-2dfd-4147-9ea0-40a6edecee08
-- title:
--   Proposition 3.1(i): $\Psi\in\Gamma_0(X\oplus\mathbb R)$
-- statement:
--   Let $X$ be a reflexive real Banach space, let $\varphi\in\Gamma_0(\mathbb R)$ be a nonconstant increasing function, and let $f\in\Gamma_0(X)$ be such that $(\operatorname{dom}\varphi)\cap f(\operatorname{dom} f)\ne\varnothing$. Then the perturbation (3.1) of $\varphi\circ f$,
--   $$\Psi(x,\xi)=\begin{cases}\varphi(f(x)+\xi), & f(x)+\xi\in\operatorname{dom}\varphi;\\ +\infty, & \text{otherwise},\end{cases}$$
--   belongs to $\Gamma_0(X\oplus\mathbb R)$.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 3.1(i), p.10

import Mathlib
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_Psi

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Proposition 3.1(i)**, p.10: let `X` be a
reflexive real Banach space, `φ ∈ Γ₀(ℝ)` a nonconstant increasing function and `f ∈ Γ₀(X)` with
`(dom φ) ∩ f(dom f) ≠ ∅`, and let `Ψ` be the perturbation (3.1) of `φ ∘ f`. Then
`Ψ ∈ Γ₀(X ⊕ ℝ)`.

**Formalization Note.** `X ⊕ ℝ` is the Lean product `X × ℝ` (product topology = the topology of
the norm (2.2)). -/
theorem proposition_3_1_i {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (φ : ℝ → EReal) (hφ : TensorAHPE.IsProperClosedConvex φ)
    (hnc : ∃ a b : ℝ, φ a ≠ φ b)
    (hmono : Monotone φ) (f : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f)
    (hdom : ∃ x : X, f x ≠ ⊤ ∧ φ (f x).toReal ≠ ⊤) :
    TensorAHPE.IsProperClosedConvex (Psi φ f) := by sorry

end PertComp
