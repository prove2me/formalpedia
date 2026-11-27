-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_proof_073feb9c2335
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_proof_073feb9c2335
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:13:48.755641+00:00
-- url     : https://prove2.me/theorems/35ae7926-99e0-5a3b-94aa-f85a1054c80f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus proof 073feb9c2335: P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus proof 073feb9c2335
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus proof 073feb9c2335 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Torus Modulus proof 073feb9c2335 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusModulus.lean#L79-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PTorusModulus.lean#L79-L153

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsRadicalTorusModulus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PTorusModulus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_proof_073feb9c2335 (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v)
    (h3 : ComplementForm.Statement h) (h4 : StabilizerLevi.Statement h v)
    (h5 : UnipotentModulus.Statement h v) (h6 : RadicalTorusModulus.Statement h v)
    (h7 : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (n : ℕ)
      (v' : Basis (Fin n) E (hypComplement h x₀ w₀)),
      SemidirectHaar.Statement (archUnitary h v) (archUnitary h' v')) :
    TorusModulus.Statement h v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«TorusModulus».«proof» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_TorusModulus_proof_073feb9c2335
