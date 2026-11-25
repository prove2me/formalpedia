-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_embM_inj
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_embM_inj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:08.56744+00:00
-- url     : https://prove2.me/theorems/dfd51e54-a18b-434e-b9b1-03ceee151c50
-- title:
--   Multiplicative Heights: sdd emb M inj
-- statement:
--   The Multiplicative Heights construction uses the sdd emb M inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L142-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L142-L166

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_embM_inj {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (b : Fin k → Fin r → K) (hb : LinearIndependent K b) : Function.Injective (embM σ b).mulVec := by sorry
