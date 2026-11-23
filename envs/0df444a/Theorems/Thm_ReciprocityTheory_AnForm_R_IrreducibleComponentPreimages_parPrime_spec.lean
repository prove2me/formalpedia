-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_parPrime_spec
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.parPrime_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:50.840139+00:00
-- url     : https://prove2.me/theorems/dd6e4a61-a3e0-4896-a55b-40ca29f99194
-- title:
--   Irreducible Component Preimages: par Prime spec
-- statement:
--   The Irreducible Component Preimages construction uses the par Prime spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L81-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {p : Ideal A} [p.IsPrime]
  [IsLocalization.AtPrime S p] [IsRegularLocalRing S] {n : ℕ} {f : Fin n → A}
variable (S)

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.parPrime_spec (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n) :
    (parPrime (S := S) f i).IsPrime ∧ parPrime (S := S) f i ≤ p ∧ f i ∈ parPrime (S := S) f i := by sorry
