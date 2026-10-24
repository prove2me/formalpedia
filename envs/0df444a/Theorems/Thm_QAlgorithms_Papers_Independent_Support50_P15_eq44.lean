-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq44
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq44
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:47:32.989985+00:00
-- url     : https://prove2.me/theorems/cc2fe2ea-b692-4745-87d2-4237fff7f89f
-- title:
--   eq44
-- statement:
--   Let $d\ge2$, $H$ be Hermitian, $T>0$, and $\rho_i$ a normalized full-rank state. Put $\rho_f=e^{-H/T}/\operatorname{tr}(e^{-H/T})$, $\Delta S=S(\rho_f)-S(\rho_i)$, and let $W=F(\rho_i)-F(\rho_f)$ be available work, identified with the process supremum in Eqs. (41)--(43). For every $N\ge N(d)$,
--
--   $$W\ge TM(-\Delta S,d)\ge TN(e^{-\Delta S/N}-1+\Delta S/N).$$
--
--   For a fixed local dimension $l\ge2$ and temperature $T>0$, consider any sequence of such systems with $d_n=l^n$ and entropy-density changes $\Delta S_n/n\to\Delta s$. Then
--
--   $$\liminf_{n\to\infty}W_n\ge2T\left(\frac{\Delta s}{\log l}\right)^2.$$
--
--   The liminf is in the extended real order, so unbounded work sequences are retained. The printed asymptotic sign does not supply the coefficient-two bound in every finite dimension.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 13, eq44

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eq. (44), PDF p.13. The printed asymptotic sign is not a finite-d inequality with coefficient 2.
The liminf takes place in EReal, retaining unbounded work sequences. -/
theorem eq44 :
    (∀ d : ℕ, 2 ≤ d → ∀ h : Matrix (Fin d) (Fin d) ℂ, h.IsHermitian →
      ∀ t : ℝ, 0 < t → ∀ a : EntropyState d, fullRank a.val →
      (t : EReal) * tightBound d (-difference (thermalFinite h t) a.val) ≤ (availableWork h t a : EReal) ∧
      (∀ n : ℝ, maxVariance d ≤ n →
        ((t * exponentialBound n (-difference (thermalFinite h t) a.val) : ℝ) : EReal) ≤
          (t : EReal) * tightBound d (-difference (thermalFinite h t) a.val))) ∧
    (∀ (l : ℕ), 2 ≤ l → ∀ t : ℝ, 0 < t →
      ∀ (h : (n : ℕ) → Matrix (Fin (l ^ n)) (Fin (l ^ n)) ℂ)
        (a : (n : ℕ) → EntropyState (l ^ n)),
      (∀ n, (h n).IsHermitian ∧ fullRank (a n).val) →
      ∀ s : ℝ, Tendsto (fun n : ℕ => difference (thermalFinite (h n) t) (a n).val / n) atTop (nhds s) →
        ((2 * t * (s / Real.log l) ^ 2 : ℝ) : EReal) ≤
          Filter.liminf (fun n => (availableWork (h n) t (a n) : EReal)) atTop) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
