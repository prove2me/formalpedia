-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiDegIdx_mem_coordLat
-- name    : ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.mem_coordLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:47.22953+00:00
-- url     : https://prove2.me/theorems/7a189deb-80c8-4e58-ad61-96848d3d65f3
-- title:
--   Semi Deg Idx: mem coord Lat
-- statement:
--   The Semi Deg Idx construction uses the mem coord Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L65-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegC.lean#L65-L66

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

theorem ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.mem_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {t : Fin k → K} : t ∈ coordLat B b ↔ combMap b t ∈ B := by sorry
