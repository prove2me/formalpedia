-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P34_adjacent_tv_quantitative
-- name    : QAlgorithms.Papers.Independent.Extend50.P34.adjacent_tv_quantitative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:15:04.287444+00:00
-- url     : https://prove2.me/theorems/709b686e-1bde-48d7-8522-c917ce11e1a4
-- title:
--   Theorem 5.11
-- statement:
--   For an absolute $b>0$, throughout $n=r^2/\omega^2$ and $200\le\omega\le\sqrt r$, set $C=\lceil3\log(10r)/\log(\omega/10)\rceil$. Then
--
--   $$d_{\rm TV}(\mathrm{SW}_r^n,\mathrm{SW}_{r+1}^n)\le\exp(bC^{2.01})\omega^{-2}.$$
--
--   The $\omega^{-2}$ factor improves on the $\omega^{-1}$ obtained from Pinsker alone. This supports the extension from adjacent ranks to a rank gap $\Delta$.
-- source:
--   Quantum Spectrum Testing, arXiv:1501.05028v1, PDF p. 52, Theorem 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P34

noncomputable section

open scoped Matrix BigOperators

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P34

attribute [local instance] Classical.propDecidable

-- Reuse exact pinned definitions; these are imports, not local declarations.

open QAlgorithms.Papers.Independent.Support50.P38 (tv wordMass)

open QAlgorithms.Papers.Independent.Advance50.P28 (counts)

/-- Theorem 5.11, arXiv:1501.05028v1, PDF p.52. C is computed from r,omega; it is not arbitrary. Universal b precedes all regime parameters. -/
theorem adjacent_tv_quantitative
    : ∃ b : ℝ, 0 < b ∧ ∀ r n : ℕ, ∀ omega : ℝ,
      RankRegime r n omega → adjacentTV r n ≤
        Real.exp (b*Real.rpow (truncation r omega) (201/100 : ℝ))/omega^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P34

end
