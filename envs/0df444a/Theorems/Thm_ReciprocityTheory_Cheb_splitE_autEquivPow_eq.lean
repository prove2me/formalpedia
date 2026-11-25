-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitE_autEquivPow_eq
-- name    : ReciprocityTheory.Cheb.splitE_autEquivPow_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:12.790322+00:00
-- url     : https://prove2.me/theorems/75e93f4f-82fb-54f5-adfd-3aeb9a56eb05
-- title:
--   Cheb: split E aut Equiv Pow eq
-- statement:
--   The Cheb construction uses the split E aut Equiv Pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L16-L31

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

theorem ReciprocityTheory.Cheb.splitE_autEquivPow_eq (hirr : Irreducible (Polynomial.cyclotomic l E))
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) :
    ((IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr σ : (ZMod l)ˣ) : ZMod l) = (m : ZMod l) := by sorry
