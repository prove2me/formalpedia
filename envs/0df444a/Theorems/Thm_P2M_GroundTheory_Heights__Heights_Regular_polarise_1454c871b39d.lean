-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_polarise_1454c871b39d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_polarise_1454c871b39d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:36.171036+00:00
-- url     : https://prove2.me/theorems/f3ef2ccc-e025-47a5-9e89-dbff61cfe9ba
-- title:
--   P2 M Ground Theory Heights  Heights Regular polarise 1454c871b39d: P2 M Ground Theory Heights  Heights Regular polarise 1454c871b39d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular polarise 1454c871b39d construction uses the P2 M Ground Theory Heights  Heights Regular polarise 1454c871b39d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L270-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L270-L293

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_polarise_1454c871b39d {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : Mᵀ = M) (p q : Fin g) :
    (((fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single p 1 + Pi.single q 1 : Fin g → ℤ) k : ℂ)) -
        ((fun k => ((Pi.single p 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single p 1 : Fin g → ℤ) k : ℂ)) -
        ((fun k => ((Pi.single q 1 : Fin g → ℤ) k : ℂ)) ⬝ᵥ
          M *ᵥ fun k => ((Pi.single q 1 : Fin g → ℤ) k : ℂ))) / 2 = M p q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«polarise» := P2M_GroundTheory_Heights__Heights_Regular_polarise_1454c871b39d
