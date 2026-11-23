-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_dedekindZeta_eq_idealZetaR
-- name    : ReciprocityTheory.Cheb.dedekindZeta_eq_idealZetaR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:52.982133+00:00
-- url     : https://prove2.me/theorems/155fa870-d166-4f65-a6bb-7b7f289eb86c
-- title:
--   Cheb: dedekind Zeta eq ideal Zeta R
-- statement:
--   The Cheb construction uses the dedekind Zeta eq ideal Zeta R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L55-L59

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

theorem ReciprocityTheory.Cheb.dedekindZeta_eq_idealZetaR (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E (s : ℂ) = ((idealZetaR E s : ℝ) : ℂ) := by sorry
