-- Prove2me | Theorems.Thm_PertComp_proposition_3_1_ii
-- name    : PertComp.proposition_3_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:55.518202+00:00
-- url     : https://prove2.me/theorems/8890bd74-733f-4f1d-add3-04de1f66d41b
-- title:
--   Proposition 3.1(ii): the Lagrangian $\mathscr L_\Psi$ (3.2)
-- statement:
--   In the setting of Proposition 3.1 ($X$ a reflexive real Banach space, $\varphi\in\Gamma_0(\mathbb R)$ nonconstant increasing, $f\in\Gamma_0(X)$ with $(\operatorname{dom}\varphi)\cap f(\operatorname{dom} f)\ne\varnothing$, and $\Psi$ the perturbation (3.1)), the Lagrangian $\mathscr L_\Psi(x,\xi^*)=\inf_{\xi\in\mathbb R}(\Psi(x,\xi)-\xi\xi^*)$ is, for every $(x,\xi^*)\in X\times\mathbb R$,
--   $$\mathscr L_\Psi(x,\xi^*)=\begin{cases}+\infty, & x\notin\operatorname{dom} f;\\ (\xi^*\odot f)(x)-\varphi^*(\xi^*), & x\in\operatorname{dom} f\ \text{and}\ \xi^*\in\operatorname{dom}\varphi^*;\\ -\infty, & x\in\operatorname{dom} f\ \text{and}\ \xi^*\notin\operatorname{dom}\varphi^*.\end{cases}$$
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
--   - encoding: φ*, ∂φ and ∂φ* with ℝ* identified with ℝ; the real dual variable ξ* → PWDB.conj φ (the conjugate on the inner-product space ℝ, ⟨t, s⟩ = t s), subdiffR, and realDual ξ* = (ξ ↦ ξ ξ*) as the element of StrongDual ℝ ℝ; reason: canonical isomorphism ℝ ≅ ℝ*; same values
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 3.1(ii), (3.2), p.10

import Mathlib
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_Psi
import Definitions.Def_PertComp_lag
import Definitions.Def_PWDB_conj
import Definitions.Def_PertComp_odot

namespace PertComp

open Classical in
/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Proposition 3.1(ii)**, (3.2), p.10: in the
setting of Proposition 3.1 (`X` reflexive real Banach, `φ ∈ Γ₀(ℝ)` nonconstant increasing,
`f ∈ Γ₀(X)`, `(dom φ) ∩ f(dom f) ≠ ∅`, `Ψ` of (3.1)), the Lagrangian of `Ψ` is
`𝓛_Ψ(x, ξ*) = +∞` if `x ∉ dom f`; `(ξ* ⊙ f)(x) − φ*(ξ*)` if `x ∈ dom f` and `ξ* ∈ dom φ*`;
`−∞` if `x ∈ dom f` and `ξ* ∉ dom φ*`.

**Formalization Note.** `𝓛_Ψ` is the Lagrangian (2.24) (`lag`) with `U = ℝ`; the real dual
variable `ξ*` enters as `realDual ξ* = (ξ ↦ ξ ξ*)`. `φ*` is the published
`PWDB.conj φ` on `ℝ` (`φ*(s) = sup_t (t s − φ(t))`). -/
theorem proposition_3_1_ii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hX : IsReflexive X) (φ : ℝ → EReal) (hφ : TensorAHPE.IsProperClosedConvex φ)
    (hnc : ∃ a b : ℝ, φ a ≠ φ b)
    (hmono : Monotone φ) (f : X → EReal) (hf : TensorAHPE.IsProperClosedConvex f)
    (hdom : ∃ x : X, f x ≠ ⊤ ∧ φ (f x).toReal ≠ ⊤) (x : X) (ξ' : ℝ) :
    lag (Psi φ f) x (realDual ξ') =
      if f x = ⊤ then ⊤
      else if PWDB.conj φ ξ' ≠ ⊤ then odot ξ' f x - PWDB.conj φ ξ'
      else ⊥ := by sorry

end PertComp
