-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_countable_unitaryGroup_379daacf6d24
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_countable_unitaryGroup_379daacf6d24
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:19:28.495039+00:00
-- url     : https://prove2.me/theorems/5b59e00a-07d4-4944-beb2-2849bd2708ef
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume countable unitary Group 379daacf6d24: P2 M Ground Theory Heights  Heights Finite Covolume countable unitary Group 379daacf6d24
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume countable unitary Group 379daacf6d24 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume countable unitary Group 379daacf6d24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdelicCovolumeFinite.lean#L35-L42

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_countable_unitaryGroup_379daacf6d24 (h : HermitianForm F E W) (v : Basis ι E W) :
    Countable h.unitaryGroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«countable_unitaryGroup» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_countable_unitaryGroup_379daacf6d24
