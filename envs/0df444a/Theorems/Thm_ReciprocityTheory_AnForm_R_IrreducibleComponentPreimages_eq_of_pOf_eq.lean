-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_eq_of_pOf_eq
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_pOf_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:03:02.620991+00:00
-- url     : https://prove2.me/theorems/e868b12b-7b01-4f4e-b926-d75c8d4d0f62
-- title:
--   Irreducible Component Preimages: eq of p Of eq
-- statement:
--   The Irreducible Component Preimages construction uses the eq of p Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L143-L148

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
noncomputable section
variable {W : Scheme.{0}} {U : W.Opens}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_pOf_eq (hU : IsAffineOpen U) {z z' : W} (hz : z ∈ U) (hz' : z' ∈ U)
    (h : hU.primeIdealOf ⟨z, hz⟩ = hU.primeIdealOf ⟨z', hz'⟩) : z = z' := by sorry
