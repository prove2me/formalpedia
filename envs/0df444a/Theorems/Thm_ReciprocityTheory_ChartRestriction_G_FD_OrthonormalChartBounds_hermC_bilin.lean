-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_OrthonormalChartBounds_hermC_bilin
-- name    : ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.hermC_bilin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:27:42.577121+00:00
-- url     : https://prove2.me/theorems/bdca9455-7b51-46e0-9e51-3cffee0c418d
-- title:
--   Orthonormal Chart Bounds: herm C bilin
-- statement:
--   The Orthonormal Chart Bounds construction uses the herm C bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L72-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermCOrthonormalCoordinates.lean#L72-L79

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LowBlock
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermCOrthonormalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.hermC_bilin (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) {n : ℕ} (p q : Fin n → ℂ)
    (f : Fin n → Fin r → ℂ) :
    hermC τ G (∑ i, p i • f i) (∑ j, q j • f j) =
      ∑ i, ∑ j, p i * hermC τ G (f i) (f j) * conj (q j) := by sorry
