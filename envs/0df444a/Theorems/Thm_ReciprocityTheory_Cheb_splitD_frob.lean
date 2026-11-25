-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitD_frob
-- name    : ReciprocityTheory.Cheb.splitD_frob
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:30.61838+00:00
-- url     : https://prove2.me/theorems/c97b34ad-b610-4707-8aee-25fd87846216
-- title:
--   Cheb: split D frob
-- statement:
--   The Cheb construction uses the split D frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitD.lean#L30-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitD.lean#L30-L77

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.splitD_frob (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    ∃ σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E,
      σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
        IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ Nrm q ∧
      ∀ x : 𝓞 (CyclotomicField l E), ∃ y : 𝓞 (CyclotomicField l E),
        (y : CyclotomicField l E) = σ (x : CyclotomicField l E) ∧ y - x ^ Nrm q ∈ P.asIdeal := by sorry
