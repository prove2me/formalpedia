-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_iM_unit
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.iM_unit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:09.008229+00:00
-- url     : https://prove2.me/theorems/3af69777-2cd5-4b9a-a71e-2df90dd10251
-- title:
--   Place Perm Operator Bicommutant Span: i M unit
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the i M unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L110-L114

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.iM_unit {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) :
    cT s (pm 1 0 0 1 0 U) * hypJ J * pm 1 0 0 1 0 U = hypJ J := by sorry
