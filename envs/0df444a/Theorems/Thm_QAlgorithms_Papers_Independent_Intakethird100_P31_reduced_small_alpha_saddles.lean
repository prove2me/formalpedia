-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P31_reduced_small_alpha_saddles
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P31.reduced_small_alpha_saddles
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T06:42:32.769055+00:00
-- url     : https://prove2.me/theorems/61ee2d38-dd6f-44c5-84be-9da03e2fa6ff
-- title:
--   Two small-alpha roots of the reduced near-four-dimensional gap equation
-- statement:
--   Let $N\ge1$ be an integer, $0<\epsilon<2$, and $n>0$. Consider the retained small-$\alpha$ equation of (6.33),
--
--   $$Q_{\epsilon,n}(\alpha)=\frac\alpha n+\frac{\alpha^2}{\epsilon}-\frac16\left(\frac1{n^2}-1\right)=0,$$
--
--   and put $\Delta=\epsilon^2+\frac23\epsilon(1-n^2)$. Its real roots are exactly
--
--   $$\alpha_\pm=-\frac\epsilon{2n}\pm\frac{\sqrt\Delta}{2n},\qquad \Delta\ge0.$$
--
--   There are no real roots when $\Delta<0$. At $\Delta=0$ the two displayed branches coincide. Under the retained normalization $d=N\alpha^2/(8\pi^2\epsilon)$, their amplitudes are
--
--   $$d_\pm=\frac{N}{8\pi^2}\left[\frac16\left(\frac1{n^2}-1\right)+\frac{\epsilon\mp\sqrt\Delta}{2n^2}\right].$$
--
--   The exact threshold of this reduced equation is $n_c(\epsilon)=\sqrt{1+3\epsilon/2}$, with $\lim_{\epsilon\downarrow0}(n_c(\epsilon)-1)/\epsilon=3/4$.
--
--   These are the roots and amplitudes of the specified asymptotic truncation, not exact roots or amplitudes of the full integral saddle equation.
-- source:
--   Entanglement Entropy in the O(N) model, arXiv:0904.4477v1, PDF p. 37, §VI (6.32)–(6.35): two small-alpha saddles near four dimensions

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P31

noncomputable section

open Filter Set MeasureTheory

open scoped Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P31

/-- PDF p.37, (6.33)--(6.35): complete real roots and corresponding
amplitudes of the retained small-alpha equation. Zero discriminant is
coalescence, not two simple roots. Its exact reduced threshold has leading
shift `3*eps/4`. These roots are not asserted to solve (6.25) exactly. -/
theorem reduced_small_alpha_saddles (N : ℕ) (hN : 0 < N)
    (eps n : ℝ) (heps : 0 < eps) (hD : eps < 2) (hn : 0 < n) :
    (∀ alpha : ℝ, reducedGap eps n alpha = 0 ↔
      0 ≤ reducedDiscriminant eps n ∧
        (alpha = reducedRoot eps n true ∨ alpha = reducedRoot eps n false)) ∧
    (0 ≤ reducedDiscriminant eps n ↔ n ≤ Real.sqrt (1 + 3 * eps / 2)) ∧
    (0 ≤ reducedDiscriminant eps n →
      ((reducedRoot eps n true = reducedRoot eps n false ↔
          reducedDiscriminant eps n = 0) ∧
       (∀ plus : Bool,
         reducedAmplitude N eps (reducedRoot eps n plus) =
           (N : ℝ) / (8 * Real.pi ^ 2) *
             ((1 / n ^ 2 - 1) / 6 +
               (eps - (if plus then 1 else -1) *
                 Real.sqrt (reducedDiscriminant eps n)) / (2 * n ^ 2))))) ∧
    Tendsto (fun e : ℝ => (Real.sqrt (1 + 3 * e / 2) - 1) / e)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 / 4 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P31

end
