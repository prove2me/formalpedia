-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitC_bound
-- name    : ReciprocityTheory.Cheb.splitC_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:49:15.633129+00:00
-- url     : https://prove2.me/theorems/a7fe6b64-703d-4f19-91c6-a01d4173e04e
-- title:
--   Cheb: split C bound
-- statement:
--   The Cheb construction uses the split C bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitC.lean#L36-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitC.lean#L36-L61

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

theorem ReciprocityTheory.Cheb.splitC_bound (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (S : Set (Prm E)) (hS : S.Finite)
    (h : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard) (s : ℝ) (hs : 1 < s) :
    (k : ℝ) * PE E s ≤ PE E' s + k * hS.toFinset.card := by sorry
