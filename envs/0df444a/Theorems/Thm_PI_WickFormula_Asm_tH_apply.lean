-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_tH_apply
-- name    : PI.WickFormula.Asm.tH_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:06.268513+00:00
-- url     : https://prove2.me/theorems/89eee0fc-ae55-426e-afdc-6725afc5e73e
-- title:
--   Asm: t H apply
-- statement:
--   The Asm construction uses the t H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L63-L65

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

theorem PI.WickFormula.Asm.tH_apply (h1 : OrdLin) (a : Fin r → AA) (a' : Fin s → AA) (κ : Fin r → Fin s → k) (σ₀ : M)
    (n : ℕ) (R : MvPolynomial (Fin r ⊕ Fin s) k) :
    tH h1 a a' κ σ₀ n R = ordEval a a' ((n.factorial : ℚ)⁻¹ • (delta κ ^ n) R) • σ₀ := by sorry
