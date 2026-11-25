-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_embMat_injective
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiPt.embMat_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:02:01.151911+00:00
-- url     : https://prove2.me/theorems/09ef6a1e-c1ba-5d17-9ef6-c4a46413bfb7
-- title:
--   Semi Pt: emb Mat injective
-- statement:
--   The Semi Pt construction uses the emb Mat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L207-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegE.lean#L207-L231

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ReciprocityTheory.MultiplicativeHeights.SemiPt.embMat_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (hli : LinearIndependent K b) :
    Function.Injective (embMat σ b).mulVec := by sorry
