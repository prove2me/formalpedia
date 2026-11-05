-- Prove2me | Theorems.Thm_RockafellianRelax_eq_A1_argmin_tilt_iff
-- name    : RockafellianRelax.eq_A1_argmin_tilt_iff
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:37:21.274985+00:00
-- url     : https://prove2.me/theorems/a3ee2e36-4b6d-4beb-8362-cfbf73827aa5
-- title:
--   (A.1), proof of Proposition 3.3 — joint minimizers of $f(u,x) - \langle\bar y,u\rangle$ split into $u$ and $x$
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ with min-value function $\mathcal V(u) = \inf_x f(u,x)$, and $\bar y \in \mathbb R^m$. For all $u^\star \in \mathbb R^m$, $x^\star \in \mathbb R^n$,
--
--   $$
--   (u^\star, x^\star) \in \operatorname*{argmin}_{u,x}\bigl\{f(u,x) - \langle\bar y,u\rangle\bigr\}
--   \iff
--   u^\star \in \operatorname*{argmin}_u\bigl\{\mathcal V(u) - \langle\bar y,u\rangle\bigr\}
--   \ \text{ and }\
--   x^\star \in \operatorname*{argmin}_x f(u^\star, x).
--   $$
--
--   Every argmin contains only points where the function is $< +\infty$. This is the step of the proof of Proposition 3.3 that reduces the joint problem to the min-value function.
--
--   Differences from the source:
--   - encoding: f a Rockafellian for (3.1) (the context of the statement) → f : ℝᵐ × ℝⁿ → R̄ arbitrary; reason: every f is a Rockafellian for φ := f(0, ·), and φ does not occur in the statement, so no instance changes
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Proof of Proposition 3.3, display (A.1), p.36

import Mathlib
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_minValue
import Definitions.Def_RockafellianRelax_tilt

namespace RockafellianRelax

/-- **Splitting the joint argmin**, display (A.1). Royset, Chen & Eckstrand, arXiv:2204.04762v4,
Proof of Proposition 3.3, display (A.1), p.36: "(u⋆, x⋆) ∈ argmin_{u,x} f(u, x) − ⟨ȳ, u⟩ ⇐⇒
u⋆ ∈ argmin_u 𝒱(u) − ⟨ȳ, u⟩, x⋆ ∈ argmin_x f(u⋆, x)."

**Formalization Note.** Every `argmin` carries the domain condition of p.6 (value `< +∞`). In the
paper `f` is a Rockafellian for (3.1); every `f` is a Rockafellian for `φ := f(0, ·)` and `φ` does
not occur in (A.1), so `f` is arbitrary here. -/
theorem eq_A1_argmin_tilt_iff {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (ybar : Fin m → ℝ) (us : Fin m → ℝ) (xs : Fin n → ℝ) :
    (us, xs) ∈ argmin (tilt f ybar) ↔
      us ∈ argmin (fun u : Fin m → ℝ => minValue f u - ((ybar ⬝ᵥ u : ℝ) : EReal)) ∧
        xs ∈ argmin (fun x : Fin n → ℝ => f (us, x)) := by sorry

end RockafellianRelax
