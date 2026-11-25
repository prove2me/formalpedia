-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isBranch_iff
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isBranch_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:28.356459+00:00
-- url     : https://prove2.me/theorems/12b216b2-2e90-453a-8731-d288572ad766
-- title:
--   Irreducible Component Preimages: is Branch iff
-- statement:
--   The Irreducible Component Preimages construction uses the is Branch iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L151-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L151-L166

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}
variable {Z : W.IdealSheafData} {U : W.Opens} {hU : IsAffineOpen U} {y : W} {hy : y ∈ U} {n : ℕ}
  {f : Fin n → Γ(W, U)} {J : Finset (Fin n)} {q : Fin n → PrimeSpectrum Γ(W, U)}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isBranch_iff (hq : ParPrimes hU hy f q)
    (hZU : Z.ideal ⟨U, hU⟩ = Ideal.span {∏ i ∈ J, f i}) {i : Fin n} (hi : i ∈ J) (C : Set W) :
    IsBranchH (Z.support : Set W) (f i) y C ↔ C = closure {hU.fromSpec (q i)} := by sorry
