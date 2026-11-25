-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_splitE_split_ext
-- name    : ReciprocityTheory.Cheb.splitE_split_ext
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:34.096831+00:00
-- url     : https://prove2.me/theorems/966521f5-7156-56c2-943c-3455c29d741b
-- title:
--   Cheb: split E split ext
-- statement:
--   The Cheb construction uses the split E split ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitE.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/SplitE.lean#L9-L18

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitE
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

theorem ReciprocityTheory.Cheb.splitE_split_ext (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : Algebra E E') (k : ℕ), 2 ≤ k ∧
      ∀ q : Prm E, ¬ l ∣ Nrm q → χ ((Nrm q : ℕ) : ZMod l) = 1 →
        k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by sorry
