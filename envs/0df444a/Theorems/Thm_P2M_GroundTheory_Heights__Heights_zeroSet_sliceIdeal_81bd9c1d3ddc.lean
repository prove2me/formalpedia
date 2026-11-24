-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc
-- name    : P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:24.930794+00:00
-- url     : https://prove2.me/theorems/3a846a73-6781-439b-928c-353d127bbb5a
-- title:
--   P2 M Ground Theory Heights  Heights zero Set slice Ideal 81bd9c1d3ddc: P2 M Ground Theory Heights  Heights zero Set slice Ideal 81bd9c1d3ddc
-- statement:
--   The P2 M Ground Theory Heights  Heights zero Set slice Ideal 81bd9c1d3ddc construction uses the P2 M Ground Theory Heights  Heights zero Set slice Ideal 81bd9c1d3ddc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceObjects.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceObjects.lean#L24-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
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
open MvPolynomial Matrix ComplexSets
noncomputable section
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) : zeroSet (sliceIdeal J L q) = zeroSet J ∩ {x | L *ᵥ x = L *ᵥ q} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«zeroSet_sliceIdeal» := P2M_GroundTheory_Heights__Heights_zeroSet_sliceIdeal_81bd9c1d3ddc
