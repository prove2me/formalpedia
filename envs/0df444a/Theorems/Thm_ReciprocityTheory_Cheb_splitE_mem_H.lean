-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitE_mem_H
-- name    : ReciprocityTheory.Cheb.splitE_mem_H
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:46.272032+00:00
-- url     : https://prove2.me/theorems/71f1d98f-0971-4b33-af87-c09b75c445f5
-- title:
--   Cheb: split E mem H
-- statement:
--   The Cheb construction uses the split E mem H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L33-L42

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem ReciprocityTheory.Cheb.splitE_mem_H (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) (hm : χ (m : ZMod l) = 1) :
    σ ∈ splitEH hirr χ := by sorry
