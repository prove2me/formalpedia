-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_pt_smul
-- name    : ReciprocityTheory.ChartRestriction.L1.pt_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:46:06.176206+00:00
-- url     : https://prove2.me/theorems/2c4296f1-6231-44b7-978a-a377ac1ee7cb
-- title:
--   L1: pt smul
-- statement:
--   The L1 construction uses the pt smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFacSlash.lean#L26-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModFacSlash.lean#L26-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModBasic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModFacSlash
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.pt_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    pt t.1 t.2.1 t.2.2 (γ • τ) = γ' • pt t'.1 t'.2.1 t'.2.2 τ ∧
      denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * denom γ τ := by sorry
