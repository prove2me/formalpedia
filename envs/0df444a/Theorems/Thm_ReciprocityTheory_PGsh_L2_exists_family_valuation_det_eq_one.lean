-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_family_valuation_det_eq_one
-- name    : ReciprocityTheory.PGsh.L2.exists_family_valuation_det_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:51.858795+00:00
-- url     : https://prove2.me/theorems/a83c6027-24b5-4137-b7fc-cf4c8161b744
-- title:
--   L2: exists family valuation det eq one
-- statement:
--   The L2 construction uses the exists family valuation det eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFamilyValuationDetEqOne.lean#L113-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsFamilyValuationDetEqOne.lean#L113-L223

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetLeOneOfEntriesIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
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

theorem ReciprocityTheory.PGsh.L2.exists_family_valuation_det_eq_one (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
    (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j)) :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ x, v (h3mm K β f x).det = 1 := by sorry
