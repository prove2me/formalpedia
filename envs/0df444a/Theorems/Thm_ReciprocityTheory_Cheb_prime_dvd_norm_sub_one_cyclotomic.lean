-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_prime_dvd_norm_sub_one_cyclotomic
-- name    : ReciprocityTheory.Cheb.prime_dvd_norm_sub_one_cyclotomic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:26.096468+00:00
-- url     : https://prove2.me/theorems/ecfa9228-7522-4bb6-84e3-920fe8e67276
-- title:
--   Cheb: prime dvd norm sub one cyclotomic
-- statement:
--   The Cheb construction uses the prime dvd norm sub one cyclotomic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitA.lean#L11-L25

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

theorem ReciprocityTheory.Cheb.prime_dvd_norm_sub_one_cyclotomic (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l) : l ∣ Nrm P - 1 := by sorry
