-- Prove2me | Theorems.Thm_VolunteerNotify_dual_feasibility
-- name    : VolunteerNotify.dual_feasibility
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:38:41.929859+00:00
-- url     : https://prove2.me/theorems/2b6c0015-e62d-43e1-9f6f-eb01901791e1
-- title:
--   (12)–(16), p.20 — the tight dual solution with $\mu=1/(2-q)$ is feasible
-- statement:
--   Let $x\in\mathcal P$, let $v$ be a volunteer, $q$ the MDHR of $g$ and $\mu=1/(2-q)$. Take $\gamma_t=\mu$ for all $t$, $\alpha_1=1-\mu$, and for $2\le t\le T$
--   $$
--   \alpha_t=\alpha_{t-1}+\gamma_{t-1}-\gamma_t-\gamma_{t-1}\sum_{s}\lambda_{s,t-1}x_{v,s,t-1}+\sum_{t'=1}^{t-1}\gamma_{t'}\sum_{s}\lambda_{s,t'}x_{v,s,t'}\,g(t-t').
--   $$
--   Then $\mu\in[1/2,1]$ and $\alpha_t\ge 0$ for all $t$.
--
--   Together with tightness of the constraints, this is feasibility in (Dual) of Table 1. It is the step that turns the hazard rate into the factor $1/(2-q)$.
--
--   Differences from the source:
--   - generalization: q is the minimum over τ ∈ ℕ of the hazard rates (Definition 1) → q is their infimum (`mdhr`); reason: the minimum need not exist, e.g. hazards 1/2 + 1/(τ+2); the infimum equals the minimum whenever it exists, so the statement specializes to the source
--   - encoding: sums over s = 0, …, S → sums over `Fin S`; reason: variables of type 0 are 0 (fn. 18, p.16), so the s = 0 terms vanish
--   - encoding: indices in [a] = {1, …, a} → `Fin a`, paper index = value + 1, a = 0 allowed; reason: Lean convention; at a = 0 the sums are empty and no instance of the source changes
--   - generalization: the page argues with x* of (5) → any x ∈ P; reason: only x* ∈ P is used, at line (16); x* ∈ P, so the statement specializes to the source
--   - encoding: α, γ given by the displayed recursion, with all constraints tight → `α γ : Fin T → ℝ` with hypotheses γ_t = µ, α_1 = 1 − µ and the recursion; reason: the hypotheses determine α and γ by recursion on t; the conclusion is the page's non-negativity, and γ_t = µ ≥ 0 follows from µ ∈ [1/2, 1]
--   - encoding: Z > 0 with law g, τ ∈ ℕ → `g : ℕ → ℝ` with `g 0 = 0`, τ ranges over positive integers; reason: ℕ is {1, 2, …} in the source; same instances
-- source:
--   Manshadi, Rodilitz, Online Policies for Efficient Volunteer Crowdsourcing, arXiv:2002.08474v7, (12)–(16), p.20; (Dual), Table 1, p.19

import Mathlib
import Definitions.Def_VolunteerNotify_lpValue

namespace VolunteerNotify

/-- Dual feasibility, Manshadi–Rodilitz, arXiv:2002.08474v7, (12)–(16), p.20: for `x ∈ P` and
`µ = 1/(2 − q)`, the tight solution `γ_t = µ`, `α_1 = 1 − µ` and, for `t ≥ 2`,

  `α_t = α_{t−1} + γ_{t−1} − γ_t − γ_{t−1} ∑_s λ_{s,t−1} x_{v,s,t−1} + ∑_{t'=1}^{t−1} γ_{t'} ∑_s λ_{s,t'} x_{v,s,t'} g(t − t')`

has `µ ∈ [1/2, 1]` and `α_t ≥ 0` for all `t`.

**Formalization Note.** `t'` below is paper period `t − 1`, `Finset.Iic t'` is `{1, …, t − 1}`,
and the `s = 0` terms of the page vanish because `x_{v,0,t} = 0` (fn. 18, p.16). -/
theorem dual_feasibility {V S T : ℕ} (I : Instance V S T) (x : Decision V S T)
    (hx : x ∈ feasibleSet I) (v : Fin V) (mu : ℝ) (hmu : mu = 1 / (2 - mdhr I.g))
    (γ α : Fin T → ℝ) (hγ : ∀ t, γ t = mu)
    (hα₁ : ∀ t : Fin T, (t : ℕ) = 0 → α t = 1 - mu)
    (hα : ∀ t t' : Fin T, (t : ℕ) = (t' : ℕ) + 1 →
      α t = α t' + γ t' - γ t - γ t' * ∑ s, I.lam s t' * x v s t' +
        ∑ u ∈ Finset.Iic t', γ u * ∑ s, I.lam s u * x v s u * I.g ((t : ℕ) - (u : ℕ))) :
    mu ∈ Set.Icc (1 / 2 : ℝ) 1 ∧ ∀ t, 0 ≤ α t := by sorry

end VolunteerNotify
