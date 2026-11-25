-- Prove2me | Theorems.Thm_PI_WickFormula_Asm_factorial_smul
-- name    : PI.WickFormula.Asm.factorial_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:44:19.499871+00:00
-- url     : https://prove2.me/theorems/fff063c1-a363-4eb6-a4bb-97085d5f3cb8
-- title:
--   Asm: factorial smul
-- statement:
--   The Asm construction uses the factorial smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L78-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/WickFormula/XdegLeTotalDegree.lean#L78-L84

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

theorem PI.WickFormula.Asm.factorial_smul (n : ℕ) (S : MvPolynomial (Fin r ⊕ Fin s) k) :
    (((n + 1).factorial : ℚ)⁻¹ • ((n + 1) • S)) = ((n.factorial : ℚ)⁻¹ • S) := by sorry
