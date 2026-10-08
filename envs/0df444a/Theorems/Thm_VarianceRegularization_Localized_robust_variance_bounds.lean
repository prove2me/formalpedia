-- Prove2me | Theorems.Thm_VarianceRegularization_Localized_robust_variance_bounds
-- name    : VarianceRegularization.Localized.robust_variance_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:43:06.292924+00:00
-- url     : https://prove2.me/theorems/2e8d876b-9496-4297-a12a-f97314778a27
-- title:
--   Theorem 1, (10) — the robust risk lies within 2Mρ/n below the standard-deviation expansion
-- statement:
--   Let $z_1,\dots,z_n$ be real numbers in $[M_0,M_1]$, $n\ge1$, and let $M=M_1-M_0$. Write $\mathbb E_{\widehat P_n}[Z]=\frac1n\sum_iz_i$ for their mean and $s_n^2=\mathbb E_{\widehat P_n}[Z^2]-\mathbb E_{\widehat P_n}[Z]^2$ for their variance. Fix $\rho\ge0$. Then
--   $$
--   \Big(\sqrt{\frac{2\rho}{n}s_n^2}-\frac{2M\rho}{n}\Big)_+\ \le\ \sup_P\Big\{\mathbb E_P[Z] : D_\phi(P\|\widehat P_n)\le\frac\rho n\Big\}-\mathbb E_{\widehat P_n}[Z]\ \le\ \sqrt{\frac{2\rho}{n}s_n^2}.
--   $$
--
--   The robust risk is therefore the empirical mean plus a standard-deviation penalty, up to an error of order $M\rho/n$; the proof of Theorem 4 uses the lower bound.
--
--   **Formalization Note** The statement is deterministic: it holds for every vector of values in $[M_0,M_1]$, which is how the paper applies it at the realized sample. The supremum is over weight vectors on the sample in the $\chi^2$ ball.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 7, Theorem 1, inequality (10)

import Mathlib
import Definitions.Def_UnderstandingML_Rademacher
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity

open MeasureTheory ProbabilityTheory

namespace VarianceRegularization.Localized

/-- **Theorem 1, inequality (10)** (p. 7). Let `z₁, …, z_n` be values in `[M₀, M₁]`, `M = M₁ − M₀`,
with empirical mean `E_{P̂_n}[Z]` and empirical variance `s_n² = E_{P̂_n}[Z²] − E_{P̂_n}[Z]²`. Fix
`ρ ≥ 0`. Then
`(√(2ρ s_n²/n) − 2Mρ/n)₊ ≤ sup_{P : D_φ(P‖P̂_n) ≤ ρ/n} E_P[Z] − E_{P̂_n}[Z] ≤ √(2ρ s_n²/n)`.
The statement is deterministic in the sample. -/
theorem robust_variance_bounds (n : ℕ) (hn : 0 < n) (M0 M1 ρ : ℝ) (hρ : 0 ≤ ρ)
    (z : Fin n → ℝ) (hz : ∀ i, z i ∈ Set.Icc M0 M1) :
    max (Real.sqrt (2 * ρ / n * empVar z (fun x => x)) - 2 * (M1 - M0) * ρ / n) 0
        ≤ VarianceRegularization.Expansion.robustSup n ρ z - empMean z (fun x => x) ∧
      VarianceRegularization.Expansion.robustSup n ρ z - empMean z (fun x => x)
        ≤ Real.sqrt (2 * ρ / n * empVar z (fun x => x)) := by sorry

end VarianceRegularization.Localized
