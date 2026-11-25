-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_ThreeTorsionChord_chordBig
-- name    : ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord.chordBig
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:38.527152+00:00
-- url     : https://prove2.me/theorems/9bef4a76-a6b7-5d1d-ad46-c9dc1d106a3c
-- title:
--   Three Torsion Chord: chord Big
-- statement:
--   The Three Torsion Chord construction uses the chord Big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorsUnit3.lean#L33-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorsUnit3.lean#L33-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorsUnit3
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord
open Formalism.ELL.FormalGroupPointsTorsion
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem ReciprocityTheory.ChartRestriction.L1.ThreeTorsionChord.chordBig {x y x2 y2 m : K} (h2 : ‖(2 : K)‖ = 1) (hx : ‖x‖ < 1) (hy : ‖y‖ = 1)
    (hx2 : ‖x2‖ < 1) (hy2 : ‖y2 + y‖ < 1) (hne : x2 ≠ x) (hm : m = (y2 - y) / (x2 - x)) :
    1 < ‖m ^ 2 - x2 - x‖ := by sorry
