-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_re_nonneg_befb807dcc93
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_re_nonneg_befb807dcc93
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:43:02.164194+00:00
-- url     : https://prove2.me/theorems/56e5e22d-0a5d-4653-942e-4ed3b28e060e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Len Sq re nonneg befb807dcc93: P2 M Ground Theory Heights  Heights Finite Covolume Len Sq re nonneg befb807dcc93
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Len Sq re nonneg befb807dcc93 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Len Sq re nonneg befb807dcc93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenSq.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLenSq.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLenSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_re_nonneg_befb807dcc93 {P : Matrix ι ι ℂ} (hP : P.PosDef) (y : ι → ℂ) :
    0 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LenSq».«re_nonneg» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LenSq_re_nonneg_befb807dcc93
