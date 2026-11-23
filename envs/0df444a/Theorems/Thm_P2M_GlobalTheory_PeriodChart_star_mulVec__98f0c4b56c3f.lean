-- Prove2me | Theorems.Thm_P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f
-- name    : P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:36.156509+00:00
-- url     : https://prove2.me/theorems/1e78ee4c-344b-43cf-8658-7bff65f2f52d
-- title:
--   P2 M Global Theory Period Chart star mul Vec  98f0c4b56c3f: P2 M Global Theory Period Chart star mul Vec  98f0c4b56c3f
-- statement:
--   The P2 M Global Theory Period Chart star mul Vec  98f0c4b56c3f construction uses the P2 M Global Theory Period Chart star mul Vec  98f0c4b56c3f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L235-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L235-L238

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}

theorem P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f (B : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    star (B *ᵥ w) = B.map (starRingEnd ℂ) *ᵥ star w := by sorry

alias «GlobalTheory».«PeriodChart».«star_mulVec'» := P2M_GlobalTheory_PeriodChart_star_mulVec__98f0c4b56c3f
