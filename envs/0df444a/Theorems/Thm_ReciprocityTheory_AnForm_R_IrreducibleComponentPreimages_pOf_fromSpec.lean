-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_pOf_fromSpec
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.pOf_fromSpec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:31.93217+00:00
-- url     : https://prove2.me/theorems/c08ba55d-ed17-5a5e-9638-468c3b68b706
-- title:
--   Irreducible Component Preimages: p Of from Spec
-- statement:
--   The Irreducible Component Preimages construction uses the p Of from Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L154-L156

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.pOf_fromSpec (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(W, U)) :
    hU.primeIdealOf ⟨hU.fromSpec P, fromSpec_mem hU P⟩ = P := by sorry
