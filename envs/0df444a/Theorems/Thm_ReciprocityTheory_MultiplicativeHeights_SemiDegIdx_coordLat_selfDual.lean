-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_coordLat_selfDual
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_selfDual
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:02:30.459302+00:00
-- url     : https://prove2.me/theorems/73f60b2f-f0fb-4960-9f05-e7bd4f10c4b1
-- title:
--   Semi Deg Idx: coord Lat self Dual
-- statement:
--   The Semi Deg Idx construction uses the coord Lat self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L130-L136

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField Matrix
open scoped nonZeroDivisors

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_selfDual {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hb : IsKBasisIn B b)
    (hsd : IsSelfDual S B) : IsSelfDual (coordForm S b) (coordLat B b) := by sorry
