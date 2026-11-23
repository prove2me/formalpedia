-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_blk_inj
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.blk_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:07.904796+00:00
-- url     : https://prove2.me/theorems/953a5fd0-a5bc-4bf2-877f-3345c1ca11a0
-- title:
--   Place Perm Operator Bicommutant Span: blk inj
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the blk inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L26-L32

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.blk_inj {a b c d a' b' c' d' : K} {r s u w r' s' u' w' : Fin M → K} {U U' : Matrix (Fin M) (Fin M) K}
    (h : blk a b r c d s u w U = blk a' b' r' c' d' s' u' w' U') :
    a = a' ∧ b = b' ∧ r = r' ∧ c = c' ∧ d = d' ∧ s = s' ∧ u = u' ∧ w = w' ∧ U = U' := by sorry
