-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_exists_class_cont
-- name    : ReciprocityTheory.Cheb.exists_class_cont
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:53.927363+00:00
-- url     : https://prove2.me/theorems/cefe2759-fe05-5176-a15e-71f42ccdd306
-- title:
--   Cheb: exists class cont
-- statement:
--   The Cheb construction uses the exists class cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L100-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/KHoldA.lean#L100-L106

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.Cheb.exists_class_cont {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, Summable (gfun χ c s) →
      ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
        ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * F s := by sorry
