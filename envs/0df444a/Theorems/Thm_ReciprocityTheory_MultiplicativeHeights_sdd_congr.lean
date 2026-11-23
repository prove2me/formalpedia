-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_congr
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_congr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:46.451167+00:00
-- url     : https://prove2.me/theorems/db135413-1385-4e14-8909-dce678f9b8b5
-- title:
--   Multiplicative Heights: sdd congr
-- statement:
--   The Multiplicative Heights construction uses the sdd congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L63-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L63-L71

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_congr {n : ℕ} (B X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit B.det) :
    X = Bᴴ * ((B⁻¹)ᴴ * X * B⁻¹) * B ∧
    ∀ w : Fin n → ℂ, star w ⬝ᵥ (((B⁻¹)ᴴ * X * B⁻¹) *ᵥ w) =
      star (B⁻¹ *ᵥ w) ⬝ᵥ (X *ᵥ (B⁻¹ *ᵥ w)) := by sorry
