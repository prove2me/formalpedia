-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_usual_plus_probability
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.usual_plus_probability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:17:06.212653+00:00
-- url     : https://prove2.me/theorems/08d74ffb-2d2c-4ace-b42a-2ca6e375f932
-- title:
--   Lemma 5.15
-- statement:
--   In the standing regime, set $C=\lceil3\log(10r)/\log(\omega/10)\rceil$. Call a diagram usual-plus if it is usual using the same threshold $10r/\omega$ and satisfies $|L_\infty^*|\le2$. For an absolute $b>0$, under either law $\mathrm{SW}_r^n$ or $\mathrm{SW}_{r+1}^n$,
--
--   $$\Pr[\lambda\text{ not usual-plus}]\le\exp(bC^{2.01})/\omega^4.$$
--
--   The same event is used for both distributions. This controls the exceptional part in the TV comparison.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 54, Lemma 5.15

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Lemma 5.15, arXiv:1501.05028v1, PDF p.54. The p.55 proof says ≤2 when naming the bad event; the definition and Markov argument require >2. Both laws use the same r-based UsualPlus predicate. -/
theorem usual_plus_probability
    : ∃ b : ℝ, 0 < b ∧ ∀ r n : ℕ, ∀ omega : ℝ,
      RankRegime r n omega →
        event (n := n) (unif r) (fun lambda => ¬ UsualPlus r omega lambda) ≤
          Real.exp (b*Real.rpow (truncation r omega) (201/100 : ℝ))/omega^4 ∧
        event (n := n) (unif (r+1)) (fun lambda => ¬ UsualPlus r omega lambda) ≤
          Real.exp (b*Real.rpow (truncation r omega) (201/100 : ℝ))/omega^4 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
