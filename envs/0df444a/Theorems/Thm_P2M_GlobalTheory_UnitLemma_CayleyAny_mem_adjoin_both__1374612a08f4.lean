-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_CayleyAny_mem_adjoin_both__1374612a08f4
-- name    : P2M_GlobalTheory_UnitLemma_CayleyAny_mem_adjoin_both__1374612a08f4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:42.017773+00:00
-- url     : https://prove2.me/theorems/44d01fad-289e-553a-aa15-8f782e2ee5a3
-- title:
--   P2 M Global Theory Unit Lemma Cayley Any mem adjoin both  1374612a08f4: P2 M Global Theory Unit Lemma Cayley Any mem adjoin both  1374612a08f4
-- statement:
--   The P2 M Global Theory Unit Lemma Cayley Any mem adjoin both  1374612a08f4 construction uses the P2 M Global Theory Unit Lemma Cayley Any mem adjoin both  1374612a08f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaResiduallyUnipotentCayleyTransform.lean#L13-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaResiduallyUnipotentCayleyTransform.lean#L13-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase

theorem P2M_GlobalTheory_UnitLemma_CayleyAny_mem_adjoin_both__1374612a08f4 {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (g Y : A) (ξ a b : O) (Q : O[X])
    (hQm : Q.Monic) (hQ : aeval g Q = 0) (hQs : IsUnit (Q.eval ξ)) (hab : IsUnit (ξ * a - b))
    (hY : Y * (g - algebraMap O A ξ) = algebraMap O A a * g - algebraMap O A b) :
    Y ∈ Algebra.adjoin O ({g} : Set A) ∧ g ∈ Algebra.adjoin O ({Y} : Set A) := by sorry

alias «GlobalTheory».«UnitLemma».«CayleyAny».«mem_adjoin_both'» := P2M_GlobalTheory_UnitLemma_CayleyAny_mem_adjoin_both__1374612a08f4
