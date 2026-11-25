-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_cyc_re_psum_upper
-- name    : ReciprocityTheory.Cheb.cyc_re_psum_upper
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:56.047475+00:00
-- url     : https://prove2.me/theorems/8589863a-7dd1-586f-89cb-2d7edac51c84
-- title:
--   Cheb: cyc re psum upper
-- statement:
--   The Cheb construction uses the cyc re psum upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/TendstoLogOneDivSubOne.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/TendstoLogOneDivSubOne.lean#L18-L35

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

theorem ReciprocityTheory.Cheb.cyc_re_psum_upper (h2 : E2) (h3a : CasimirPowerSurjectiveSymmetric) (hK : KProp)
    (hirr : Irreducible (Polynomial.cyclotomic l E)) (χ : DirichletCharacter ℂ l) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), χ ≠ 1 → (Psum E χ s).re ≤ C := by sorry
