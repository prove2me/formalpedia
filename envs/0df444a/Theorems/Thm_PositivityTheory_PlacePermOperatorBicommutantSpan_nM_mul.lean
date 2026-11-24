-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_nM_mul
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.nM_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:01.299112+00:00
-- url     : https://prove2.me/theorems/6e1228d0-281c-42cc-b5af-ddc0952f18fb
-- title:
--   Place Perm Operator Bicommutant Span: n M mul
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the n M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L122-L126

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.nM_mul (w w' : Fin M → K) (z z' : K) :
    nM s J w z * nM s J w' z' = nM s J (w + w') (z + z' - hform s J w w') := by sorry
