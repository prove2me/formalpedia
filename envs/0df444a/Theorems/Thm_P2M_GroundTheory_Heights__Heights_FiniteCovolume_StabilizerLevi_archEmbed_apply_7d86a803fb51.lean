-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_archEmbed_apply_7d86a803fb51
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_archEmbed_apply_7d86a803fb51
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:50.455064+00:00
-- url     : https://prove2.me/theorems/31585f53-7acf-4ca2-8602-50b110c02d8a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi arch Embed apply 7d86a803fb51: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi arch Embed apply 7d86a803fb51
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi arch Embed apply 7d86a803fb51 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi arch Embed apply 7d86a803fb51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L57-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_archEmbed_apply_7d86a803fb51 (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (w : InfinitePlace E) :
    (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«archEmbed_apply» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_archEmbed_apply_7d86a803fb51
