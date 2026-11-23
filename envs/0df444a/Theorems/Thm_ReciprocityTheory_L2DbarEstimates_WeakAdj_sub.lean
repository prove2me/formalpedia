-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_WeakAdj_sub
-- name    : ReciprocityTheory.L2DbarEstimates.WeakAdj.sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:04.246969+00:00
-- url     : https://prove2.me/theorems/1eff19fa-f11b-45da-89de-8c6f84131a8d
-- title:
--   Weak Adj: sub
-- statement:
--   The Weak Adj construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/HormanderLemma.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/MinimalSolutions/HormanderLemma.lean#L27-L30

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace
variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

theorem ReciprocityTheory.L2DbarEstimates.WeakAdj.sub {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f - f') (w - w') := by sorry
