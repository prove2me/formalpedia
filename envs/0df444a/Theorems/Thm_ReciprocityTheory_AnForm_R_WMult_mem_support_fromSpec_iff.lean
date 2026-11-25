-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_WMult_mem_support_fromSpec_iff
-- name    : ReciprocityTheory.AnForm.R.WMult.mem_support_fromSpec_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:59.613272+00:00
-- url     : https://prove2.me/theorems/01ba662a-890a-4fe8-8c01-40f7feaad029
-- title:
--   WMult: mem support from Spec iff
-- statement:
--   The WMult construction uses the mem support from Spec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultA.lean#L33-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WMultA.lean#L33-L43

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}

theorem ReciprocityTheory.AnForm.R.WMult.mem_support_fromSpec_iff (I : W.IdealSheafData) (U : W.affineOpens) (hU : IsAffineOpen U.1)
    (P : PrimeSpectrum Γ(W, U.1)) :
    hU.fromSpec P ∈ (I.support : Set W) ↔ I.ideal U ≤ P.asIdeal := by sorry
