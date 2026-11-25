-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_norm_coprime_of_not_dvd_under
-- name    : ReciprocityTheory.Cheb.norm_coprime_of_not_dvd_under
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:07.158041+00:00
-- url     : https://prove2.me/theorems/f9b98aaf-3ae5-438f-a04c-3a631bb698ed
-- title:
--   Cheb: norm coprime of not dvd under
-- statement:
--   The Cheb construction uses the norm coprime of not dvd under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L27-L34

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

theorem ReciprocityTheory.Cheb.norm_coprime_of_not_dvd_under (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) : Nat.Coprime (Nrm P) l := by sorry
