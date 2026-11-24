-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:18.166828+00:00
-- url     : https://prove2.me/theorems/f4fc611c-d25a-498c-901e-f88dd379f70f
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Extend mem zero Locus incidence Ideal a3506a649f6c: P2 M Ground Theory Heights  Heights Chow Form Extend mem zero Locus incidence Ideal a3506a649f6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Extend mem zero Locus incidence Ideal a3506a649f6c construction uses the P2 M Ground Theory Heights  Heights Chow Form Extend mem zero Locus incidence Ideal a3506a649f6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean#L22-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormExtend
variable {F : Type*} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c {E : Type*} [Field E] [Algebra F E]
    (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) (z : (Fin k × Fin n) ⊕ Fin n → E) :
    z ∈ zeroLocus E (incidenceIdeal I k) ↔
      (∀ g ∈ I, aeval (z ∘ Sum.inr) g = 0) ∧ ∀ i, ∑ j, z (Sum.inl (i, j)) * z (Sum.inr j) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormExtend».«mem_zeroLocus_incidenceIdeal» := P2M_GroundTheory_Heights__Heights_ChowFormExtend_mem_zeroLocus_incidenceIdeal_a3506a649f6c
