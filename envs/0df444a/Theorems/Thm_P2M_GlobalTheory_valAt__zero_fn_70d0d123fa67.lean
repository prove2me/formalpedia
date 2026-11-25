-- Prove2me | Theorems.Thm_P2M_GlobalTheory_valAt__zero_fn_70d0d123fa67
-- name    : P2M_GlobalTheory_valAt__zero_fn_70d0d123fa67
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:05.835824+00:00
-- url     : https://prove2.me/theorems/780627a2-f815-45b8-b38f-d4c69e1156fd
-- title:
--   P2 M Global Theory val At  zero fn 70d0d123fa67: P2 M Global Theory val At  zero fn 70d0d123fa67
-- statement:
--   The P2 M Global Theory val At  zero fn 70d0d123fa67 construction uses the P2 M Global Theory val At  zero fn 70d0d123fa67 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsAHOfPolarisation.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsAHOfPolarisation.lean#L17-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsAHOfPolarisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem P2M_GlobalTheory_valAt__zero_fn_70d0d123fa67 {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by sorry

alias «GlobalTheory».«valAt'_zero_fn» := P2M_GlobalTheory_valAt__zero_fn_70d0d123fa67
