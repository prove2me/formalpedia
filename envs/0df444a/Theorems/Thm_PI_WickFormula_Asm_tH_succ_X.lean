-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_tH_succ_X
-- name    : PI.WickFormula.Asm.tH_succ_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:59.890799+00:00
-- url     : https://prove2.me/theorems/ac43b9c4-0862-505b-857e-d445501f7840
-- title:
--   Asm: t H succ X
-- statement:
--   The Asm construction uses the t H succ X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L108-L116

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

theorem PI.WickFormula.Asm.tH_succ_X (h1 : OrdLin) (h2 : OrdX) (g1 : Gen.PowXL) (g2 : Gen.CommL) (H : Hyp a b a' b' κ σ₀)
    (i : Fin r) (n : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ (n + 1) (X (Sum.inl i) * R) =
      a i • tH h1 a a' κ σ₀ (n + 1) R + tH h1 a a' κ σ₀ n (Gen.dL κ i R) := by sorry
