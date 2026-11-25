-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_cc_ordEval_mem
-- name    : ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_ordEval_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:51.483053+00:00
-- url     : https://prove2.me/theorems/1840d2a0-1396-5cb9-96ce-b339209406eb
-- title:
--   SCPf: cc ord Eval mem
-- statement:
--   The SCPf construction uses the cc ord Eval mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXEqRename.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LiftXEqRename.lean#L84-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_DivPowInteg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXEqRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.SCPf.cc_ordEval_mem (J : Submodule R k) (e : ℕ) (E0 : AA k d) (hE0 : constantCoeff E0 = 1) {r q : ℕ}
    (a : Fin r → Module.End k (AA k d)) (a' : Fin q → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (ha' : ∀ j X, GoodE R E0 X → GoodE R E0 (a' j X))
    (σ : AA k d) (hσ : GoodE R E0 σ) (Q : MvPolynomial (Fin r ⊕ Fin q) k) (hQ : ∀ mo, Q.coeff mo ∈ J ^ e) :
    constantCoeff (PI.WickFormula.ordEval a a' Q σ) ∈ J ^ e := by sorry
