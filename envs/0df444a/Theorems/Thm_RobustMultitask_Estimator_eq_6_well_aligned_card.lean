-- Prove2me | Theorems.Thm_RobustMultitask_Estimator_eq_6_well_aligned_card
-- name    : RobustMultitask.Estimator.eq_6_well_aligned_card
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:53.048764+00:00
-- url     : https://prove2.me/theorems/8266cf16-0a78-4b34-a5e3-ba1c91583526
-- title:
--   (6), p. 14 — at most s/ζ components are ζ-well-aligned
-- statement:
--   Let $\beta^1,\dots,\beta^N,\beta^\dagger\in\mathbb R^d$ satisfy the sparse heterogeneity assumption $\|\beta^j-\beta^\dagger\|_0\le s$ for every task $j\in[N]$, and let $\zeta>0$. Then the set $\mathcal I^\zeta_{\mathrm{well}}$ of $\zeta$-well-aligned components (Definition 2) satisfies
--   $$|\mathcal I^\zeta_{\mathrm{well}}|\le\frac{Ns}{N\zeta}=\frac{s}{\zeta}.$$
--
--   Out of the $Nd$ components of $\{\beta^j\}_{j\in[N]}$ at most $Ns$ differ from $\beta^\dagger$, and each well-aligned component accounts for at least $\zeta N$ of them. The bound shows that the components the trimmed mean cannot correct are few, which makes the remaining bias sparse enough for the LASSO step.
--
--   **Formalization Note** The hypothesis $\zeta>0$ is needed for the quotient $s/\zeta$; for $\zeta=0$ the bound would be false in Lean, where $s/0=0$.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 14, eq. (6)

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_Alignment

namespace RobustMultitask.Estimator

/-- Equation (6), p. 14: under sparse heterogeneity `‖βʲ − β†‖₀ ≤ s` for every task, and for
`ζ > 0`, the number of ζ-well-aligned components is at most `Ns/(Nζ) = s/ζ`. -/
theorem eq_6_well_aligned_card {N d : ℕ} (β : Fin N → Fin d → ℝ) (βdag : Fin d → ℝ) (s : ℕ)
    (ζ : ℝ) (hζ : 0 < ζ) (hsparse : ∀ j, l0 (β j - βdag) ≤ s) :
    ((wellAligned β βdag ζ).card : ℝ) ≤ (s : ℝ) / ζ := by sorry

end RobustMultitask.Estimator
