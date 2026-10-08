-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_truncation_comparison
-- name    : SmithRenewal.Elementary.truncation_comparison
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:04.926203+00:00
-- url     : https://prove2.me/theorems/4c6faf29-3859-4569-8eac-6043dc4c8288
-- title:
--   §1.2, p. 246 — the truncated process: {X_i†} is a renewal process, S_n† ≤ S_n, N_t† ≥ N_t, H†(t) ≥ H(t), ζ_t† ≤ Δ
-- statement:
--   Let $(X_i)$ be a renewal process and $\Delta > 0$. Put $X_i^\dagger = \min(X_i, \Delta)$ and denote by $S_n^\dagger, N_t^\dagger, H^\dagger(t), \zeta_t^\dagger$ the quantities of the process $(X_i^\dagger)$. Then
--
--   1. $(X_i^\dagger)$ is a renewal process;
--   2. $S_n^\dagger \le S_n$ for every $n$ and every sample point;
--   3. $N_t^\dagger \ge N_t$ for every $t$ and every sample point;
--   4. $H^\dagger(t) \ge H(t)$ for every $t$;
--   5. $\zeta_t^\dagger \le \Delta$ for every $t \ge 0$ and every sample point.
--
--   Truncation trades the original process for one with bounded lifetimes, whose residual life is bounded and whose mean is finite; this is what allows the upper bound in the elementary renewal theorem, including the case $\mu_1 = \infty$.
--
--   **Formalization Note** $\Delta > 0$ is implicit in the paper; for $\Delta \le 0$ the truncated lifetimes would vanish with positive probability. Item 5 holds everywhere for $t \ge 0$ with the convention for $\zeta_t$ on the null event $N_t^\dagger = \infty$ (there $\zeta_t^\dagger = S_1^\dagger - t$).
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §1.2, p. 246, the truncated process

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SmithRenewal.Elementary

/-- The truncated process (Smith, *Renewal Theory and Its Ramifications*, J. R. Statist. Soc. B 20(2):243–283 (1958), §1.2, p. 246, unnumbered): "If we define X_i† = X_i for
X_i ≤ Δ, and X_i† = Δ for X_i > Δ, we obtain a renewal process {X_i†}; and if we denote related
quantities in an obvious way it is clear that S_n† ≤ S_n and hence N_t† ≥ N_t, and so that
H†(t) ≥ H(t). But, clearly, ζ_t† ≤ Δ."

Formalization Note: `Δ > 0` is the paper's implicit hypothesis (it lets Δ grow); for `Δ ≤ 0`
the `X_i†` vanish with positive probability. The bound `ζ_t† ≤ Δ` is stated for times
`t ≥ 0` and at every sample point (including the null event `N_t† = ⊤`, where `zeta` is
`S_1† − t`). -/
theorem truncation_comparison {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : IsRenewalProcess P X)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    IsRenewalProcess P (trunc Δ X) ∧
    (∀ n ω, S (trunc Δ X) n ω ≤ S X n ω) ∧
    (∀ t ω, N X t ω ≤ N (trunc Δ X) t ω) ∧
    (∀ t, H X P t ≤ H (trunc Δ X) P t) ∧
    (∀ t, 0 ≤ t → ∀ ω, zeta (trunc Δ X) t ω ≤ Δ) := by sorry

end SmithRenewal.Elementary
