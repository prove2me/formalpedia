-- Prove2me | Theorems.Thm_PositivityTheory_PlacePermOperatorBicommutantSpan_gram_blk
-- name    : PositivityTheory.PlacePermOperatorBicommutantSpan.gram_blk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:24.027605+00:00
-- url     : https://prove2.me/theorems/5c3d6b18-2641-4069-9166-495d15059e87
-- title:
--   Place Perm Operator Bicommutant Span: gram blk
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the gram blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/ThetaDilations/ParAlg.lean#L84-L91

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

theorem PositivityTheory.PlacePermOperatorBicommutantSpan.gram_blk (s : K →+* K) (J : Matrix (Fin M) (Fin M) K) (a b d : K) (r t w : Fin M → K)
    (U : Matrix (Fin M) (Fin M) K) :
    cT s (blk a b r 0 d t 0 w U) * hypJ J * blk a b r 0 d t 0 w U =
      blk 0 (s a * d) (s a • t) (s d * a) (s d * b + s b * d + ((s ∘ w) ᵥ* J) ⬝ᵥ w)
        (s d • r + s b • t + ((s ∘ w) ᵥ* J) ᵥ* U) (a • (s ∘ t)) (b • (s ∘ t) + d • (s ∘ r) + (cT s U * J) *ᵥ w)
        (vecMulVec (s ∘ t) r + vecMulVec (s ∘ r) t + cT s U * J * U) := by sorry
