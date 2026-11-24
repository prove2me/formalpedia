-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_iM_nM
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.iM_nM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:00.451447+00:00
-- url     : https://prove2.me/theorems/c4bcbd74-3a0f-4f17-bbf8-af637e0337ff
-- title:
--   Place Perm Operator Bicommutant Span: i M n M
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the i M n M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L128-L132

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.iM_nM {U : Matrix (Fin M) (Fin M) K} (hU : cT s U * J * U = J) (w : Fin M → K) (z : K) :
    pm 1 0 0 1 0 U * nM s J w z = nM s J (U *ᵥ w) z * pm 1 0 0 1 0 U := by sorry
