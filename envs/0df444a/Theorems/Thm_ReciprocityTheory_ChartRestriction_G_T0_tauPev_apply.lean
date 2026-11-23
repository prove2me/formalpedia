-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_tauPev_apply
-- name    : ReciprocityTheory.ChartRestriction.G.T0.tauPev_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:39:53.667698+00:00
-- url     : https://prove2.me/theorems/d45ebde3-a2c9-4b9f-951a-fc0a088ba28c
-- title:
--   T0: tau Pev apply
-- statement:
--   The T0 construction uses the tau Pev apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/SacSuccAbove.lean#L32-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.tauPev_apply {K : Type} [Field K] {D N : ℕ} (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hpt : ∀ q : MvPolynomial (TVar D N) K, q ≠ 0 → eval₂ sg pt q ≠ 0) (q : KTp K D N) :
    tauPev sg pt hpt (algebraMap (KTp K D N) (KTf K D N) q) = eval₂ sg pt q := by sorry
