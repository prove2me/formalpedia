-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitE_H_ne_top
-- name    : ReciprocityTheory.Cheb.splitE_H_ne_top
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:50.186894+00:00
-- url     : https://prove2.me/theorems/00f5bb05-110b-563b-bf4c-0336fe7b5491
-- title:
--   Cheb: split E H ne top
-- statement:
--   The Cheb construction uses the split E H ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitEA.lean#L44-L56

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

theorem ReciprocityTheory.Cheb.splitE_H_ne_top (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l)
    (hχ : χ ≠ 1) : splitEH hirr χ ≠ ⊤ := by sorry
