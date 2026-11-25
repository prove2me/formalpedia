-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyc_psum_bdd
-- name    : ReciprocityTheory.Cheb.cyc_psum_bdd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:48.490127+00:00
-- url     : https://prove2.me/theorems/39450348-4e34-4118-b17e-c09314b670aa
-- title:
--   Cheb: cyc psum bdd
-- statement:
--   The Cheb construction uses the cyc psum bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/TendstoLogOneDivSubOne.lean#L83-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/TendstoLogOneDivSubOne.lean#L83-L111

import Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
import Definitions.Def_ReciprocityTheory_Chebotarev_CasimirPowerSurjectiveSymmetric
import Definitions.Def_ReciprocityTheory_Chebotarev_NoWind
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SummableGfun
import Definitions.Def_ReciprocityTheory_Chebotarev_PowerSeriesDiagonalLinear
import Definitions.Def_ReciprocityTheory_Chebotarev_TendstoLogOneDivSubOne
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
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem ReciprocityTheory.Cheb.cyc_psum_bdd (h1 : E1) (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (h3c : SmoothMapSeminormBound) (hK : KProp) (hS1 : S1)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) (hχ : χ ≠ 1) :
    ∃ B : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖Psum E χ s‖ ≤ B := by sorry
