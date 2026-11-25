-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_DescPf_indep_iff
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf.indep_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:04.466356+00:00
-- url     : https://prove2.me/theorems/523d15fc-02b3-477a-836e-602419e77f4f
-- title:
--   Desc Pf: indep iff
-- statement:
--   The Desc Pf construction uses the indep iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DescentStatementPf.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/DescentStatementPf.lean#L10-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DescentStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_DescentStatementPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf
open scoped TensorProduct
open Module
variable {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.DescPf.indep_iff {ι : Type} (v : ι → V) :
    LinearIndependent F v ↔ LinearIndependent F' (fun i => (1 : F') ⊗ₜ[F] v i) := by sorry
