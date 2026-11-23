-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_idealZetaR_term_eq
-- name    : ReciprocityTheory.Cheb.idealZetaR_term_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:19:49.525803+00:00
-- url     : https://prove2.me/theorems/8d1377f2-5421-43d6-86be-c97477ef28ef
-- title:
--   Cheb: ideal Zeta R term eq
-- statement:
--   The Cheb construction uses the ideal Zeta R term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L26-L34

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
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

theorem ReciprocityTheory.Cheb.idealZetaR_term_eq (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 0 < s) (n : ℕ) :
    LSeries.term (fun n ↦ (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) n =
      (((Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by sorry
