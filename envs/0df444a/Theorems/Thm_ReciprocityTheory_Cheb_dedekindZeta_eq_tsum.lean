-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_dedekindZeta_eq_tsum
-- name    : ReciprocityTheory.Cheb.dedekindZeta_eq_tsum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:24.679808+00:00
-- url     : https://prove2.me/theorems/7afeada5-f89b-4fda-bd7f-1c05217bc577
-- title:
--   Cheb: dedekind Zeta eq tsum
-- statement:
--   The Cheb construction uses the dedekind Zeta eq tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L110-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/EulerSum.lean#L110-L123

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

theorem ReciprocityTheory.Cheb.dedekindZeta_eq_tsum (E : Type) [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) :
    dedekindZeta E s = ∑' a : NZIdeal E, ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) := by sorry
