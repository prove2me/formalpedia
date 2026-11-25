-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_decomp_self
-- name    : ReciprocityTheory.ChartRestriction.G.SA.hf_decomp_self
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:23.597692+00:00
-- url     : https://prove2.me/theorems/d5ade809-359d-5c8c-aebc-cb4ce1319971
-- title:
--   SA: hf decomp self
-- statement:
--   The SA construction uses the hf decomp self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/HfDecompSelf.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/HfDecompSelf.lean#L27-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ReachableFixingAddSmulSecond
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_HfDecompSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ) {e f : ι → K} (he : hf σ J e e = 0)
  (hff : hf σ J f f = 0) (hef : hf σ J e f = 1)
include hσ hJ he hff hef

theorem ReciprocityTheory.ChartRestriction.G.SA.hf_decomp_self (x y : K) {w : ι → K} (hwe : hf σ J w e = 0) (hwf : hf σ J w f = 0) :
    hf σ J (x • e + y • f + w) (x • e + y • f + w) = x * σ y + σ x * y + hf σ J w w := by sorry
