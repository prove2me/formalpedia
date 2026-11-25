-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_unitary_06ccbf9ff635
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_unitary_06ccbf9ff635
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:22.962954+00:00
-- url     : https://prove2.me/theorems/fd10c425-8de3-46a8-a336-f85996620a36
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume vec At unitary 06ccbf9ff635: P2 M Ground Theory Heights  Heights Finite Covolume vec At unitary 06ccbf9ff635
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume vec At unitary 06ccbf9ff635 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume vec At unitary 06ccbf9ff635 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMahlerCompactness.lean#L19-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMahlerCompactness.lean#L19-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLenCauchySchwarz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StGramDetermines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMahlerCompactness
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
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_unitary_06ccbf9ff635 (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup) (x : W)
    (w : InfinitePlace E) :
    vecAt v ((γ : W ≃ₗ[E] W) x) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«vecAt_unitary» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_vecAt_unitary_06ccbf9ff635
