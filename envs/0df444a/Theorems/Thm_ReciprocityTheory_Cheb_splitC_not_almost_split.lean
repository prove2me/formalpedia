-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitC_not_almost_split
-- name    : ReciprocityTheory.Cheb.splitC_not_almost_split
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:10.257698+00:00
-- url     : https://prove2.me/theorems/a80354d1-55f1-5b05-aab9-a1d4d538ddc0
-- title:
--   Cheb: split C not almost split
-- statement:
--   The Cheb construction uses the split C not almost split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitC.lean#L63-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitC.lean#L63-L94

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
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

theorem ReciprocityTheory.Cheb.splitC_not_almost_split (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (hk : 2 ≤ k)
    (h : {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard}.Finite) : False := by sorry
