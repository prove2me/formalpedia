-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_tH_zero_X
-- name    : PI.WickFormula.Asm.tH_zero_X
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:44:31.942832+00:00
-- url     : https://prove2.me/theorems/8b625479-c3df-4697-9aaa-a010d680c68a
-- title:
--   Asm: t H zero X
-- statement:
--   The Asm construction uses the t H zero X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L101-L106

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

theorem PI.WickFormula.Asm.tH_zero_X (h1 : OrdLin) (h2 : OrdX) (H : Hyp a b a' b' κ σ₀) (i : Fin r)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ 0 (X (Sum.inl i) * R) = a i • tH h1 a a' κ σ₀ 0 R := by sorry
