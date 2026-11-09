-- Prove2me | Theorems.Thm_ProxGapTight_parameter_choice
-- name    : ProxGapTight.parameter_choice
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:49:11.928207+00:00
-- url     : https://prove2.me/theorems/c5a8b3a0-2bfa-472e-9fa8-2b2b6af707c3
-- title:
--   Proof of Theorem 3.1, p.12 — choice of $Q$, $t$, $\xi$
-- statement:
--   Let $0<\delta<1$, $J_{3/2}(\delta)<\rho<\Gamma(\delta)$, $\eta>0$, and $\eta_0=\min\{\eta,(\delta-\Gamma(\delta))/4\}$. For every $Q$ sufficiently large in terms of $\delta,\rho,\eta$ there are an integer $t\ge1$ and $\xi>0$ such that, for all sufficiently large $m$,
--   $$
--   \Phi_t\Big(\frac{e_m}{n_m}\Big)+3\xi<\rho,\qquad \Phi_t\Big(\frac{4e_m}{3n_m}\Big)-3\xi>\Gamma(\delta),
--   $$
--   and
--   $$
--   |\Phi_t(u)-\delta|<\frac{\eta_0}{2}\qquad\text{for all } u\in\Big[\frac{L_m}{n_m},\frac{3e_m}{n_m}\Big].
--   $$
--
--   These are the parameters with which the amplification $u\mapsto\Phi_t(u)$ maps the three distances of the base code of Lemma 3.2 (radius $e_m/n_m$, word distance $4e_m/(3n_m)$, code distance in $[L_m/n_m,3e_m/n_m]$) close to the targets $\rho$, $\Gamma(\delta)$ and $\delta$.
--
--   **Formalization Note** "$Q$ sufficiently large" is quantified over all natural numbers $Q\ge Q_0$; the interval is closed; $n_m,e_m,L_m$ are the integers of Lemma 3.2.
--
--   Differences from the source:
--   - generalization: Q := p^a > 32, Q ∉ {49, 121}, Q sufficiently large in terms of δ, ρ, η → every natural number Q ≥ Q₀; reason: the paper's Q are among them; the statement specializes to them
--   - reading: 'Choose a … Q sufficiently large in terms of δ, ρ, η. Choose an integer t ≥ 1 and ξ > 0 such that, for all sufficiently large m, …' → ∃ Q₀, ∀ Q ≥ Q₀, ∃ t ≥ 1, ∃ ξ > 0, ∃ m₀, ∀ m ≥ m₀, …; reason: the order of the choices in the text
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), proof of Theorem 3.1, p.12, display

import Mathlib
import Definitions.Def_ProxGapTight_J32
import Definitions.Def_ProxGapTight_Gam
import Definitions.Def_ProxGapTight_Phi
import Definitions.Def_ProxGapTight_nm
import Definitions.Def_ProxGapTight_em
import Definitions.Def_ProxGapTight_Lm

namespace ProxGapTight

/-- **Parameter choice**, proof of Theorem 3.1, Kominers, Thaler, Zheng, manuscript (Sept. 2026),
p.12, display. With `η₀ := min{η, (δ − Γ(δ))/4}`, for every `Q` sufficiently large in terms of
`δ, ρ, η` there are an integer `t ≥ 1` and `ξ > 0` such that, for all sufficiently large `m`,
`Φ_t(e_m/n_m) + 3ξ < ρ`, `Φ_t(4e_m/(3n_m)) − 3ξ > Γ(δ)` and `|Φ_t(u) − δ| < η₀/2` for all
`u ∈ [L_m/n_m, 3e_m/n_m]`.

**Formalization Note.** "`Q` sufficiently large" is `∃ Q₀, ∀ Q ≥ Q₀` over all natural numbers `Q`
(the paper's `Q = p^a > 32`, `Q ∉ {49, 121}` are among them). The interval is closed. `n_m, e_m,
L_m` are the natural-number quantities of p.7, cast to `ℝ`. -/
theorem parameter_choice (δ ρ η : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hJ : J32 δ < ρ)
    (hΓ : ρ < Gam δ) (hη : 0 < η) :
    ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ∃ t : ℕ, 1 ≤ t ∧ ∃ ξ : ℝ, 0 < ξ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Phi t ((em Q m : ℝ) / (nm Q m : ℝ)) + 3 * ξ < ρ ∧
      Gam δ < Phi t (4 * (em Q m : ℝ) / (3 * (nm Q m : ℝ))) - 3 * ξ ∧
      ∀ u ∈ Set.Icc ((Lm Q m : ℝ) / (nm Q m : ℝ)) (3 * (em Q m : ℝ) / (nm Q m : ℝ)),
        |Phi t u - δ| < min η ((δ - Gam δ) / 4) / 2 := by sorry

end ProxGapTight
