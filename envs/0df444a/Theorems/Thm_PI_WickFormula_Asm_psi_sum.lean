-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_psi_sum
-- name    : PI.WickFormula.Asm.psi_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:15.685704+00:00
-- url     : https://prove2.me/theorems/ce7ec58c-dc85-4a5a-aec2-d3271db85293
-- title:
--   Asm: psi sum
-- statement:
--   The Asm construction uses the psi sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L71-L76

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

theorem PI.WickFormula.Asm.psi_sum (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (N : ℕ) {α : Type} (t : Finset α) (g : α → MvPolynomial (Fin r ⊕ Fin s) k) :
    psi h1 a a' κ σ₀ N (∑ x ∈ t, g x) = ∑ x ∈ t, psi h1 a a' κ σ₀ N (g x) := by sorry
