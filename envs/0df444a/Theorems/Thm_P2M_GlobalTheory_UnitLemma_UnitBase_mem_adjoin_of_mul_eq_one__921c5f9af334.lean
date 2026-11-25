-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitLemma_UnitBase_mem_adjoin_of_mul_eq_one__921c5f9af334
-- name    : P2M_GlobalTheory_UnitLemma_UnitBase_mem_adjoin_of_mul_eq_one__921c5f9af334
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:11:18.1008+00:00
-- url     : https://prove2.me/theorems/14adacd2-91b3-4fa2-a820-6b9ee3fb45f6
-- title:
--   P2 M Global Theory Unit Lemma Unit Base mem adjoin of mul eq one  921c5f9af334: P2 M Global Theory Unit Lemma Unit Base mem adjoin of mul eq one  921c5f9af334
-- statement:
--   The P2 M Global Theory Unit Lemma Unit Base mem adjoin of mul eq one  921c5f9af334 construction uses the P2 M Global Theory Unit Lemma Unit Base mem adjoin of mul eq one  921c5f9af334 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L10-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L10-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial

theorem P2M_GlobalTheory_UnitLemma_UnitBase_mem_adjoin_of_mul_eq_one__921c5f9af334 {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s t : A}
    (h : s * t = 1) (ht : IsIntegral O t) : t ∈ Algebra.adjoin O {s} := by sorry

alias «GlobalTheory».«UnitLemma».«UnitBase».«mem_adjoin_of_mul_eq_one'» := P2M_GlobalTheory_UnitLemma_UnitBase_mem_adjoin_of_mul_eq_one__921c5f9af334
