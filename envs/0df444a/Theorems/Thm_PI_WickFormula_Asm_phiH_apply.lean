-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_phiH_apply
-- name    : PI.WickFormula.Asm.phiH_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:08.175256+00:00
-- url     : https://prove2.me/theorems/a78ebe12-d68b-4f4e-abf2-068ce4dbb6dd
-- title:
--   Asm: phi H apply
-- statement:
--   The Asm construction uses the phi H apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L55-L56

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

theorem PI.WickFormula.Asm.phiH_apply (h1 : OrdLin) (a b : Fin r → AA) (a' b' : Fin s → AA) (σ₀ : M)
    (R : MvPolynomial (Fin r ⊕ Fin s) k) : phiH h1 a b a' b' σ₀ R = ordEval (a + b) (a' + b') R • σ₀ := by sorry
