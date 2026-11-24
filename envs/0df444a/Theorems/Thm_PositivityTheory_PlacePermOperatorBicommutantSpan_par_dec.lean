-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_par_dec
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.par_dec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:59:02.886069+00:00
-- url     : https://prove2.me/theorems/acde67af-20b0-4f19-9da7-52f14eee5415
-- title:
--   Place Perm Operator Bicommutant Span: par dec
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the par dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L152-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L152-L177

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.par_dec (hs : ∀ x, s (s x) = x) {g : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hg : cT s g * hypJ J * g = hypJ J)
    (h0 : ∀ i : Fin (M + 1), g i.succ 0 = 0) :
    ∃ (w : Fin M → K) (z : K) (U : Matrix (Fin M) (Fin M) K) (a : Kˣ), z + s z + hform s J w w = 0 ∧
      cT s U * J * U = J ∧ g = nM s J w z * pm 1 0 0 1 0 U * pm (a : K) 0 0 (s (a⁻¹ : Kˣ)) 0 1 := by sorry
