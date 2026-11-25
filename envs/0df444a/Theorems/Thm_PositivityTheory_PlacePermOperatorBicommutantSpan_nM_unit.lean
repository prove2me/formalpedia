-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_nM_unit
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.nM_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:14.404036+00:00
-- url     : https://prove2.me/theorems/61ca8d7d-3c34-4afa-a6aa-6c43b63e8a1e
-- title:
--   Place Perm Operator Bicommutant Span: n M unit
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the n M unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L99-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L99-L108

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.nM_unit (hs : ∀ x, s (s x) = x) (hJ : cT s J = J) {w : Fin M → K} {z : K} (hz : z + s z + hform s J w w = 0) :
    cT s (nM s J w z) * hypJ J * nM s J w z = hypJ J := by sorry
