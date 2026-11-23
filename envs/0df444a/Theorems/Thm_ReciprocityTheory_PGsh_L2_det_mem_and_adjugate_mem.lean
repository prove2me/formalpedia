-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_det_mem_and_adjugate_mem
-- name    : ReciprocityTheory.PGsh.L2.det_mem_and_adjugate_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:30.699023+00:00
-- url     : https://prove2.me/theorems/2ae95ccb-26f6-43eb-a2f2-f3a42c991b15
-- title:
--   L2: det mem and adjugate mem
-- statement:
--   The L2 construction uses the det mem and adjugate mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L160-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L160-L177

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem ReciprocityTheory.PGsh.L2.det_mem_and_adjugate_mem (AA : HopfOrder (C := C) R N) {X : Type} [Fintype X] [DecidableEq X]
    (F : Matrix X X (N → C)) (hF : ∀ i j, F i j ∈ AA.carrier) :
    (fun x => (F.map fun g => g x).det) ∈ AA.carrier ∧
      ∀ i j, (fun x => (F.map fun g => g x).adjugate i j) ∈ AA.carrier := by sorry
