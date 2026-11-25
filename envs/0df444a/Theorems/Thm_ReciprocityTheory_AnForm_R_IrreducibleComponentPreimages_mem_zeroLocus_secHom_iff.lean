-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_mem_zeroLocus_secHom_iff
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.mem_zeroLocus_secHom_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:19.354869+00:00
-- url     : https://prove2.me/theorems/bd20e3b4-cb66-46cf-857d-48f7b81d2cac
-- title:
--   Irreducible Component Preimages: mem zero Locus sec Hom iff
-- statement:
--   The Irreducible Component Preimages construction uses the mem zero Locus sec Hom iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L222-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L222-L228

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}
variable {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.mem_zeroLocus_secHom_iff (P : AffPres s) (y : W) (hy : y ∈ P.V)
    (hc : IsClosed ({y} : Set W)) (g : MvPolynomial (Fin P.n) ℂ) :
    y ∈ W.zeroLocus {P.secHom g} ↔ eval (P.coord y hy) g = 0 := by sorry
