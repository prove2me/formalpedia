-- Prove2me | Theorems.Thm_PertComp_proposition_3_1_iii
-- name    : PertComp.proposition_3_1_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:49.488109+00:00
-- url     : https://prove2.me/theorems/ecf4e6a5-c157-4f55-bbe1-dc673bcf358a
-- title:
--   Proposition 3.1(iii): the Kuhn–Tucker operator $\mathscr K_\Psi$ (3.3)
-- statement:
--   In the setting of Proposition 3.1, the Kuhn–Tucker operator (2.26) of $\Psi$ is, for every $(x,\xi^*)\in X\times\mathbb R$,
--   $$\mathscr K_\Psi(x,\xi^*)=\begin{cases}\partial(\xi^*\odot f)(x)\times\big(\partial\varphi^*(\xi^*)-f(x)\big), & x\in\operatorname{dom} f\ \text{and}\ \xi^*\in\operatorname{dom}\varphi^*;\\ \varnothing, & x\notin\operatorname{dom} f\ \text{or}\ \xi^*\notin\operatorname{dom}\varphi^*,\end{cases}$$
--   a subset of $X^*\oplus\mathbb R$. Here $\partial\varphi^*(\xi^*)-f(x)=\{s-f(x) : s\in\partial\varphi^*(\xi^*)\}$.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
--   - encoding: φ*, ∂φ and ∂φ* with ℝ* identified with ℝ; the real dual variable ξ* → PWDB.conj φ (the conjugate on the inner-product space ℝ, ⟨t, s⟩ = t s), subdiffR, and realDual ξ* = (ξ ↦ ξ ξ*) as the element of StrongDual ℝ ℝ; reason: canonical isomorphism ℝ ≅ ℝ*; same values
--   - reading: (2.6) defines ∂f for proper f, while (2.26) applies ∂ to Lagrangians that can be improper → the formula (2.6) applied to every EReal-valued function (RockafellarMaxMono.Shared.subdiff); reason: this is how the paper's proofs of (3.3) and (3.12) evaluate ∂ off V and off the domain
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 3.1(iii), (3.3), p.10

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_Psi
import Definitions.Def_PertComp_lag
import Definitions.Def_PWDB_conj
import Definitions.Def_PertComp_subdiffR
import Definitions.Def_PertComp_odot

namespace PertComp

open Pointwise

open Classical in
/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Proposition 3.1(iii)**, (3.3), p.10: in the
setting of Proposition 3.1, the Kuhn–Tucker operator of `Ψ` is
`𝒦_Ψ(x, ξ*) = ∂(ξ* ⊙ f)(x) × (∂φ*(ξ*) − f(x))` if `x ∈ dom f` and `ξ* ∈ dom φ*`, and `∅` if
`x ∉ dom f` or `ξ* ∉ dom φ*`.

**Formalization Note.** `𝒦_Ψ` is (2.26) (`kt`) with `U = ℝ`, the dual variable `ξ*` entering as
`realDual ξ*`; it is a subset of `X* × ℝ`. `∂φ*(ξ*)` is the real subdifferential `subdiffR` of
`φ* = PWDB.conj φ`, and `∂φ*(ξ*) − f(x)` is the translate `{s − f(x) | s ∈ ∂φ*(ξ*)}`. -/
theorem proposition_3_1_iii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (hX : IsReflexive X) (φ : ℝ → EReal) (hφ : TensorAHPE.IsProperClosedConvex φ)
    (hnc : ∃ a b : ℝ, φ a ≠ φ b) (hmono : Monotone φ) (f : X → EReal)
    (hf : TensorAHPE.IsProperClosedConvex f)
    (hdom : ∃ x : X, f x ≠ ⊤ ∧ φ (f x).toReal ≠ ⊤) (x : X) (ξ' : ℝ) :
    kt (Psi φ f) x (realDual ξ') =
      if f x ≠ ⊤ ∧ PWDB.conj φ ξ' ≠ ⊤ then
        RockafellarMaxMono.Shared.subdiff (odot ξ' f) x ×ˢ
          (subdiffR (PWDB.conj φ) ξ' - {(f x).toReal})
      else ∅ := by sorry

end PertComp
