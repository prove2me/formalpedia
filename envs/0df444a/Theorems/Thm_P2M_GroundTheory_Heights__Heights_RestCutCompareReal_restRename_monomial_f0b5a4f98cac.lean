-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestCutCompareReal_restRename_monomial_f0b5a4f98cac
-- name    : P2M_GroundTheory_Heights__Heights_RestCutCompareReal_restRename_monomial_f0b5a4f98cac
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:57:02.784014+00:00
-- url     : https://prove2.me/theorems/d04cc30b-80d0-4b5f-89fb-300edff86ee8
-- title:
--   P2 M Ground Theory Heights  Heights Rest Cut Compare Real rest Rename monomial f0b5a4f98cac: P2 M Ground Theory Heights  Heights Rest Cut Compare Real rest Rename monomial f0b5a4f98cac
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Cut Compare Real rest Rename monomial f0b5a4f98cac construction uses the P2 M Ground Theory Heights  Heights Rest Cut Compare Real rest Rename monomial f0b5a4f98cac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompareReal.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRestCutCompareReal.lean#L30-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRestCutCompareReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestCutCompareReal

theorem P2M_GroundTheory_Heights__Heights_RestCutCompareReal_restRename_monomial_f0b5a4f98cac (f j k N : ℕ) (e : Fin N ≃ Fin j ⊕ Fin k)
    (α : Fin f × Fin N →₀ ℕ) (r : ℝ) :
    restRename f j k N e (monomial α r) = r • restTransport f j k N e (monomial α (1 : ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestCutCompareReal».«restRename_monomial» := P2M_GroundTheory_Heights__Heights_RestCutCompareReal_restRename_monomial_f0b5a4f98cac
