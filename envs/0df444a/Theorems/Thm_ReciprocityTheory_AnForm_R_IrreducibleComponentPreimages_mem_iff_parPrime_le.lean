-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_mem_iff_parPrime_le
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.mem_iff_parPrime_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:36.907551+00:00
-- url     : https://prove2.me/theorems/c314751b-7808-5214-8c94-152766c8566a
-- title:
--   Irreducible Component Preimages: mem iff par Prime le
-- statement:
--   The Irreducible Component Preimages construction uses the mem iff par Prime le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L98-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L98-L112

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.mem_iff_parPrime_le (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) (i : Fin n)
    {Q : Ideal A} [Q.IsPrime] (hQ : Q ≤ p) : f i ∈ Q ↔ parPrime (S := S) f i ≤ Q := by sorry
