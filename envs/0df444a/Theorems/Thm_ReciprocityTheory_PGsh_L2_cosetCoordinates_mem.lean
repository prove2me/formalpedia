-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_cosetCoordinates_mem
-- name    : ReciprocityTheory.PGsh.L2.cosetCoordinates_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:30.065393+00:00
-- url     : https://prove2.me/theorems/33469a18-01ba-452b-9bb4-72d8b356df6c
-- title:
--   L2: coset Coordinates mem
-- statement:
--   The L2 construction uses the coset Coordinates mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ValuationDetLeOneOfEntriesIntegral.lean#L91-L97

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

theorem ReciprocityTheory.PGsh.L2.cosetCoordinates_mem (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) [DecidablePred (· ∈ K)] (β : Matrix K K C)
    (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
    {f : N → C} (hf : f ∈ AA.carrier) (l : K) :
    (fun x => h3co K β f x l) ∈ AA.carrier := by sorry
