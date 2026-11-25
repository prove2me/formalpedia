-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitA_norm
-- name    : ReciprocityTheory.Cheb.splitA_norm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:48:44.848656+00:00
-- url     : https://prove2.me/theorems/2a725557-cd17-4cc6-86ae-e23781cc1ebe
-- title:
--   Cheb: split A norm
-- statement:
--   The Cheb construction uses the split A norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L105-L126

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
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

theorem ReciprocityTheory.Cheb.splitA_norm (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    (Nrm P = Nrm q ∧ ((Nrm q : ℕ) : ZMod l) = 1) ∨ Nrm q ^ 2 ≤ Nrm P := by sorry
