-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_OswLocFin_no_small_subgroups
-- name    : PositivityTheory.SiegelWeilFormula.OswLocFin.no_small_subgroups
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:32.528562+00:00
-- url     : https://prove2.me/theorems/618313b7-170b-4de1-9afa-a28a601923a6
-- title:
--   Osw Loc Fin: no small subgroups
-- statement:
--   The Osw Loc Fin construction uses the no small subgroups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalInvariantNeighborhoods/SmallSub.lean#L47-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalInvariantNeighborhoods/SmallSub.lean#L47-L78

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalInvariantNeighborhoods_SmallSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.OswLocFin

theorem PositivityTheory.SiegelWeilFormula.OswLocFin.no_small_subgroups {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    (χ : K → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1)
    (hn : ∀ x, ‖χ x‖ = 1) : ∃ ε > 0, ∀ t : K, ‖t‖ ≤ ε → χ t = 1 := by sorry
