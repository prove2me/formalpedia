-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_apply_val_02d3cfa618b2
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_apply_val_02d3cfa618b2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:05.98896+00:00
-- url     : https://prove2.me/theorems/2ce8f256-6cd6-4e7a-a802-a8eed712502e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume arch Embed apply val 02d3cfa618b2: P2 M Ground Theory Heights  Heights Finite Covolume arch Embed apply val 02d3cfa618b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume arch Embed apply val 02d3cfa618b2 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume arch Embed apply val 02d3cfa618b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchLatticeDiscrete.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PArchLatticeDiscrete.lean#L24-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchLatticeDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_apply_val_02d3cfa618b2 (h : HermitianForm F E W) (v : Basis ι E W) (g : h.unitaryGroup)
    (w : InfinitePlace E) :
    ((((archEmbed h v g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : GL ι ℂ) :
        Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((g : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«archEmbed_apply_val» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_apply_val_02d3cfa618b2
