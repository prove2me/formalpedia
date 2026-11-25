-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_claim
-- name    : PI.WickFormula.Asm.claim
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:01.671639+00:00
-- url     : https://prove2.me/theorems/1852d7a0-b439-5ccf-a72b-31e7fa572fca
-- title:
--   Asm: claim
-- statement:
--   The Asm construction uses the claim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L143-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L143-L193

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

theorem PI.WickFormula.Asm.claim (h1 : OrdLin) (h2 : OrdX) (h3 : Base) (h4 : BComm) (g1 : Gen.PowXL) (g2 : Gen.CommL)
    (g3 : Gen.VanL) (H : Hyp a b a' b' κ σ₀) (d : ℕ) :
    ∀ R : MvPolynomial (Fin r ⊕ Fin s) k, (∀ m ∈ R.support, xdeg m ≤ d) → ∀ N, d < N →
      phiH h1 a b a' b' σ₀ R = psi h1 a a' κ σ₀ N R := by sorry
