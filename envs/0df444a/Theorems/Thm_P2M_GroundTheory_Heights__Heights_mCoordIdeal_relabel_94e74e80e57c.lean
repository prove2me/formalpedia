-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mCoordIdeal_relabel_94e74e80e57c
-- name    : P2M_GroundTheory_Heights__Heights_mCoordIdeal_relabel_94e74e80e57c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:54:20.780026+00:00
-- url     : https://prove2.me/theorems/2b055182-b43f-52a9-9ce4-363a108cde36
-- title:
--   P2 M Ground Theory Heights  Heights m Coord Ideal relabel 94e74e80e57c: P2 M Ground Theory Heights  Heights m Coord Ideal relabel 94e74e80e57c
-- statement:
--   The P2 M Ground Theory Heights  Heights m Coord Ideal relabel 94e74e80e57c construction uses the P2 M Ground Theory Heights  Heights m Coord Ideal relabel 94e74e80e57c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L346-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L346-L362

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_mCoordIdeal_relabel_94e74e80e57c {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) :
    mCoordIdeal (y ∘ relabelBlocks ε h) = (mCoordIdeal y).comap (relabelRingEquiv ε h) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mCoordIdeal_relabel» := P2M_GroundTheory_Heights__Heights_mCoordIdeal_relabel_94e74e80e57c
