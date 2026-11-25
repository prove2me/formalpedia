-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_PrincipalLat_isIntegral_pi__b1b6cca95627
-- name    : P2M_GlobalTheory_UnitLemma_PrincipalLat_isIntegral_pi__b1b6cca95627
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:59.665103+00:00
-- url     : https://prove2.me/theorems/7864c3d8-5837-4ef3-837d-dce8a7d129e9
-- title:
--   P2 M Global Theory Unit Lemma Principal Lat is Integral pi  b1b6cca95627: P2 M Global Theory Unit Lemma Principal Lat is Integral pi  b1b6cca95627
-- statement:
--   The P2 M Global Theory Unit Lemma Principal Lat is Integral pi  b1b6cca95627 construction uses the P2 M Global Theory Unit Lemma Principal Lat is Integral pi  b1b6cca95627 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebra.lean#L13-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLat

theorem P2M_GlobalTheory_UnitLemma_PrincipalLat_isIntegral_pi__b1b6cca95627 {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by sorry

alias «GlobalTheory».«UnitLemma».«PrincipalLat».«isIntegral_pi'» := P2M_GlobalTheory_UnitLemma_PrincipalLat_isIntegral_pi__b1b6cca95627
