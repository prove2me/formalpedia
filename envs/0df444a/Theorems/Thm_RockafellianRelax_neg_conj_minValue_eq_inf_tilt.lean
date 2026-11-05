-- Prove2me | Theorems.Thm_RockafellianRelax_neg_conj_minValue_eq_inf_tilt
-- name    : RockafellianRelax.neg_conj_minValue_eq_inf_tilt
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:58.450539+00:00
-- url     : https://prove2.me/theorems/71597bf6-4dff-440f-9e70-ef046d6aa5d3
-- title:
--   §3.1, p.7 — $-\mathcal V^*(\bar y) = \inf_{u,x} f(u,x) - \langle\bar y,u\rangle \le \mathcal V(0)$: Rockafellian relaxation is a relaxation
-- statement:
--   Let $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ with min-value function $\mathcal V(u) = \inf_x f(u,x)$, and let $\bar y \in \mathbb R^m$. Then
--
--   $$
--   -\mathcal V^*(\bar y) = \inf_{u, x}\bigl\{f(u,x) - \langle \bar y, u\rangle\bigr\}
--   \qquad\text{and}\qquad
--   \mathcal V(0) \ge -\mathcal V^*(\bar y).
--   $$
--
--   So the relaxed problem $\operatorname{minimize}_{u,x} f(u,x) - \langle\bar y,u\rangle$ (3.2) has optimal value at most that of the actual problem, for every $\bar y$: it is a relaxation.
--
--   Differences from the source:
--   - encoding: f a Rockafellian for (3.1) (the context of the statement) → f : ℝᵐ × ℝⁿ → R̄ arbitrary; reason: every f is a Rockafellian for φ := f(0, ·), and φ does not occur in the statement, so no instance changes
--   - encoding: ℝᵐ × ℝⁿ, values in R̄ = [−∞, ∞], ⟨y, u⟩ → (Fin m → ℝ) × (Fin n → ℝ) with the product topology, EReal, y ⬝ᵥ u; reason: Lean convention; same instances (the product topology has the same convergent sequences as the Euclidean norm)
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3.1, p.7 ("Since −𝒱∗(ȳ) = inf_{u,x} f(u, x) − ⟨ȳ, u⟩ … one has 𝒱(0) ≥ −𝒱∗(ȳ) always")

import Mathlib
import Definitions.Def_RockafellianRelax_conj
import Definitions.Def_RockafellianRelax_minValue
import Definitions.Def_RockafellianRelax_tilt

namespace RockafellianRelax

/-- **Rockafellian relaxation is a relaxation.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3.1,
p.7: "Since −𝒱*(ȳ) = inf_{u,x} f(u, x) − ⟨ȳ, u⟩ and the right-hand side involves joint optimization
over u and x, one has 𝒱(0) ≥ −𝒱*(ȳ) always and the relaxed problem (3.2) is indeed a relaxation of
the actual problem (3.1)."

For every `f : ℝᵐ × ℝⁿ → R̄` and `ȳ ∈ ℝᵐ`: `−𝒱*(ȳ) = inf_{u,x} f(u, x) − ⟨ȳ, u⟩` and
`𝒱(0) ≥ −𝒱*(ȳ)`.

**Formalization Note.** `𝒱*` is the conjugate (`conj`, p.7) of the min-value function
`𝒱 = minValue f`; infima and suprema in `EReal`. -/
theorem neg_conj_minValue_eq_inf_tilt {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (ybar : Fin m → ℝ) :
    -(conj (minValue f) ybar) = (⨅ p : (Fin m → ℝ) × (Fin n → ℝ), tilt f ybar p) ∧
      -(conj (minValue f) ybar) ≤ minValue f 0 := by sorry

end RockafellianRelax
