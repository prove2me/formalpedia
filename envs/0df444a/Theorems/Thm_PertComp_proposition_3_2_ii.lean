-- Prove2me | Theorems.Thm_PertComp_proposition_3_2_ii
-- name    : PertComp.proposition_3_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:00.686016+00:00
-- url     : https://prove2.me/theorems/15f7bdcd-d05f-4a97-a7fb-839dff7f175a
-- title:
--   Proposition 3.2(ii): $\mathscr P=\bigcup_{\xi^*}\{x : (x,\xi^*)\in\operatorname{zer}(\mathscr K_\Psi+\boldsymbol B)\}$
-- statement:
--   Consider the setting of Problem 1.1, the Kuhn–Tucker operator $\mathscr K_\Psi$ of Proposition 3.1(iii) and the operator
--   $$\boldsymbol B(x,\xi^*)=\Big(\big(L^*\circ((\partial g)\,\Box\,(\partial\ell))\circ L\big)(x)+\partial h(x)\Big)\times\{0\}$$
--   of (3.6). Then the set $\mathscr P$ of solutions of (1.2) is
--   $$\mathscr P=\bigcup_{\xi^*\in\mathbb R}\big\{x\in X : (x,\xi^*)\in\operatorname{zer}(\mathscr K_\Psi+\boldsymbol B)\big\}.$$
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
--   - encoding: φ*, ∂φ and ∂φ* with ℝ* identified with ℝ; the real dual variable ξ* → PWDB.conj φ (the conjugate on the inner-product space ℝ, ⟨t, s⟩ = t s), subdiffR, and realDual ξ* = (ξ ↦ ξ ξ*) as the element of StrongDual ℝ ℝ; reason: canonical isomorphism ℝ ≅ ℝ*; same values
--   - reading: (2.6) defines ∂f for proper f, while (2.26) applies ∂ to Lagrangians that can be improper → the formula (2.6) applied to every EReal-valued function (RockafellarMaxMono.Shared.subdiff); reason: this is how the paper's proofs of (3.3) and (3.12) evaluate ∂ off V and off the domain
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Proposition 3.2(ii), p.11

import Mathlib
import Definitions.Def_PertComp_Problem11
import Definitions.Def_PertComp_primalSet
import Definitions.Def_PertComp_Psi
import Definitions.Def_PertComp_lag
import Definitions.Def_PertComp_Bop

namespace PertComp

open Pointwise

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Proposition 3.2(ii)**, p.11: in the setting of
Problem 1.1, with `𝒦_Ψ` the Kuhn–Tucker operator of Proposition 3.1(iii) and `𝑩` the operator
(3.6),
`𝒫 = ⋃_{ξ* ∈ ℝ} {x ∈ X | (x, ξ*) ∈ zer (𝒦_Ψ + 𝑩)}`.

**Formalization Note.** `(x, ξ*) ∈ zer (𝒦_Ψ + 𝑩)` is `(0, 0) ∈ 𝒦_Ψ(x, ξ*) + 𝑩(x, ξ*)` (pointwise
sum of subsets of `X* × ℝ`), with `𝒦_Ψ(x, ξ*) = kt (Psi φ f) x (realDual ξ*)`. `𝒫` is
`primalSet`, the set of minimizers of (1.2). -/
theorem proposition_3_2_ii {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : ℝ → EReal) (f : X → EReal) (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal)
    (hP : Problem11 φ f g ℓ L h) :
    primalSet φ f g ℓ L h =
      ⋃ ξ' : ℝ, {x : X | ((0 : StrongDual ℝ X), (0 : ℝ)) ∈
        kt (Psi φ f) x (realDual ξ') + Bop g ℓ L h (x, ξ')} := by sorry

end PertComp
