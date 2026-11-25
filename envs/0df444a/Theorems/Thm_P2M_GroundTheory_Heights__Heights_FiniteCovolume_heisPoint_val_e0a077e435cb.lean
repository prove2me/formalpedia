-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_val_e0a077e435cb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_val_e0a077e435cb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:57:46.09053+00:00
-- url     : https://prove2.me/theorems/ec596ecf-769b-5486-b55c-7f7a146cc777
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume heis Point val e0a077e435cb: P2 M Ground Theory Heights  Heights Finite Covolume heis Point val e0a077e435cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume heis Point val e0a077e435cb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume heis Point val e0a077e435cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusCoords.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusCoords.lean#L132-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusCoords
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_val_e0a077e435cb (hp : IsHyperbolicPair h x₀ w₀) (p : HeisCoord h v x₀ w₀)
    (w : InfinitePlace E) :
    ((((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) = heisMatAt h v x₀ p.1 p.2 w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«heisPoint_val» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_heisPoint_val_e0a077e435cb
