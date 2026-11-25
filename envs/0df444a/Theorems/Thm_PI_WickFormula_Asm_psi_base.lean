-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_psi_base
-- name    : PI.WickFormula.Asm.psi_base
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:13.97181+00:00
-- url     : https://prove2.me/theorems/78c7ccf6-fc2d-5c98-b3bd-e7696a9472f3
-- title:
--   Asm: psi base
-- statement:
--   The Asm construction uses the psi base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L128-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L128-L141

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
variable {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}

theorem PI.WickFormula.Asm.psi_base (h1 : OrdLin) (g3 : Gen.VanL) (N : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k)
    (hR : ∀ m ∈ R.support, xdeg m = 0) :
    psi h1 a a' κ σ₀ (N + 1) R = ordEval a a' R • σ₀ := by sorry
