-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_exists_coset_invariant_coefficients
-- name    : ReciprocityTheory.PGsh.L2.exists_coset_invariant_coefficients
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:28:27.795602+00:00
-- url     : https://prove2.me/theorems/19b42052-add5-4a9b-927e-81c06304261b
-- title:
--   L2: exists coset invariant coefficients
-- statement:
--   The L2 construction uses the exists coset invariant coefficients property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemMapAugmentationIdealComapPullbackQuotient.lean#L80-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemMapAugmentationIdealComapPullbackQuotient.lean#L80-L143

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
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
variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)
include hv hβ hAK hf hdet

theorem ReciprocityTheory.PGsh.L2.exists_coset_invariant_coefficients {g : N → C} (hg : g ∈ AA.carrier) :
    ∃ b : K → N → C, (∀ j, b j ∈ AA.carrier) ∧ (∀ j x (k : K), b j (x + k) = b j x) ∧
      g = ∑ j, b j * f j := by sorry
