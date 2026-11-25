-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:52:35.238931+00:00
-- url     : https://prove2.me/theorems/37a8fb8c-9c76-48a3-894e-f905e9fed57b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Pair Orbits Finite proof 09504d4235de: P2 M Ground Theory Heights  Heights Finite Covolume Line Pair Orbits Finite proof 09504d4235de
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Pair Orbits Finite proof 09504d4235de construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Pair Orbits Finite proof 09504d4235de property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L92-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L92-L219

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
universe u
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type u} [AddCommGroup W] [Module E W]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (h₂ : WittPartner.Statement h)
    (h₃ : ComplementForm.Statement h) (h₄ : ComplementExtension.Statement h)
    (h₅ : AdaptedReduction.Statement h) : LinePairOrbitsFinite.Statement h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LinePairOrbitsFinite».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LinePairOrbitsFinite_proof_09504d4235de
