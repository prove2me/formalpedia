-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_eq_of_mem_parPrime
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_mem_parPrime
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:40.250915+00:00
-- url     : https://prove2.me/theorems/d3f6e87e-dde7-4bc8-a1b3-13ba88e0cc16
-- title:
--   Irreducible Component Preimages: eq of mem par Prime
-- statement:
--   The Irreducible Component Preimages construction uses the eq of mem par Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L115-L125

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_mem_parPrime (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) {i j : Fin n}
    (h : f j ∈ parPrime (S := S) f i) : j = i := by sorry
