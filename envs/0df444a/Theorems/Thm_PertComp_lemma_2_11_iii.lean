-- Prove2me | Theorems.Thm_PertComp_lemma_2_11_iii
-- name    : PertComp.lemma_2_11_iii
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:42.092836+00:00
-- url     : https://prove2.me/theorems/3648ade7-e786-4c2c-b9ee-69bdb6696a13
-- title:
--   Lemma 2.11(iii): zeros of $\mathscr K_\Phi$ solve the primal and the dual problem
-- statement:
--   Let $X$ and $U$ be reflexive real Banach spaces, let $\phi\in\Gamma_0(X)$, let $\Phi\in\Gamma_0(X\oplus U)$ be a perturbation of $\phi$, and let $\mathscr K_\Phi$ be the Kuhn–Tucker operator (2.26). If $(x,u^*)\in\operatorname{zer}\mathscr K_\Phi$, then $x$ solves the primal problem
--   $$\underset{x\in X}{\text{minimize}}\ \phi(x)$$
--   and $u^*$ solves the dual problem
--   $$\underset{u^*\in U^*}{\text{minimize}}\ \sup_{x\in X}\big(-\mathscr L_\Phi(x,u^*)\big).$$
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
--   - encoding: subgradients of a function on a dual space V* lie in V** = V → subdiffPre: the points of V whose canonical image in V** is a subgradient; reason: reflexivity identifies V** with V; same sets
--   - reading: (2.6) defines ∂f for proper f, while (2.26) applies ∂ to Lagrangians that can be improper → the formula (2.6) applied to every EReal-valued function (RockafellarMaxMono.Shared.subdiff); reason: this is how the paper's proofs of (3.3) and (3.12) evaluate ∂ off V and off the domain
--   - reading: x solves (2.23), u* solves (2.25) → x ∈ Argmin ϕ and u* ∈ Argmin of u* ↦ sup_x(−𝓛_Φ(x, u*)), minimizers inside the domain; reason: the paper's Argmin of §2, p.5; at a zero of 𝒦_Φ both values are finite
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Lemma 2.11(iii), p.9 (citing Rockafellar [50, Theorem 15])

import Mathlib
import Definitions.Def_PertComp_IsReflexive
import Definitions.Def_TensorAHPE_IsProperClosedConvex
import Definitions.Def_PertComp_lag
import Definitions.Def_RockafellianRelax_argmin

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Lemma 2.11(iii)**, p.9 (Rockafellar [50,
Theorem 15]): let `X` and `U` be reflexive real Banach spaces, `ϕ ∈ Γ₀(X)`, `Φ ∈ Γ₀(X ⊕ U)` a
perturbation of `ϕ`, and `𝒦_Φ` the Kuhn–Tucker operator (2.26). If `(x, u*) ∈ zer 𝒦_Φ`, then
`x` solves the primal problem (2.23) and `u*` solves the dual problem (2.25).

**Formalization Note.** "Solves" is membership in `Argmin` (minimizers lie in the domain, §2,
p.5; the published `RockafellianRelax.argmin`): of `ϕ` for (2.23), of
`u* ↦ sup_x (−𝓛_Φ(x, u*))` (`dualFun Φ`) for (2.25). -/
theorem lemma_2_11_iii {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (hX : IsReflexive X) (hU : IsReflexive U) (ϕ : X → EReal)
    (hϕ : TensorAHPE.IsProperClosedConvex ϕ)
    (Φ : X × U → EReal) (hΦ : TensorAHPE.IsProperClosedConvex Φ) (hpert : ∀ x : X, ϕ x = Φ (x, 0))
    (x : X) (u' : StrongDual ℝ U) (hzer : (x, u') ∈ zerKt Φ) :
    x ∈ RockafellianRelax.argmin ϕ ∧ u' ∈ RockafellianRelax.argmin (dualFun Φ) := by sorry

end PertComp
