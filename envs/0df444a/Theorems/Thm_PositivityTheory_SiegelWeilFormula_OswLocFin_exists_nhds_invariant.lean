-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_OswLocFin_exists_nhds_invariant
-- name    : PositivityTheory.SiegelWeilFormula.OswLocFin.exists_nhds_invariant
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:57:31.764652+00:00
-- url     : https://prove2.me/theorems/920d2c24-0627-4aab-aab2-fa214d8f7410
-- title:
--   Osw Loc Fin: exists nhds invariant
-- statement:
--   The Osw Loc Fin construction uses the exists nhds invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalInvariantNeighborhoods/NhdsInv.lean#L7-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalInvariantNeighborhoods/NhdsInv.lean#L7-L44

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalInvariantNeighborhoods_NhdsInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.OswLocFin
open Filter Topology

theorem PositivityTheory.SiegelWeilFormula.OswLocFin.exists_nhds_invariant {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {Φ : G → ℂ} (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ U ∈ nhds (0 : G), ∀ Y, ∀ Z ∈ U, Φ (Y + Z) = Φ Y := by sorry
