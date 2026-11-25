-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_injective_6d08bfcd17b3
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_injective_6d08bfcd17b3
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:40:33.138454+00:00
-- url     : https://prove2.me/theorems/b56514ac-640f-4d65-bd3a-7d35e1dbec9f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume arch Embed injective 6d08bfcd17b3: P2 M Ground Theory Heights  Heights Finite Covolume arch Embed injective 6d08bfcd17b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume arch Embed injective 6d08bfcd17b3 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume arch Embed injective 6d08bfcd17b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean#L17-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdelicLattices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdelicCovolumeFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_injective_6d08bfcd17b3 (h : HermitianForm F E W) (v : Basis ι E W) :
    Function.Injective (archEmbed h v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«archEmbed_injective» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_archEmbed_injective_6d08bfcd17b3
