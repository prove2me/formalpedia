-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nabVal_eq_lam
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.nabVal_eq_lam
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:07:15.147535+00:00
-- url     : https://prove2.me/theorems/e079362d-9c41-4f4a-b9f5-4b9fbd3c33bd
-- title:
--   Wick Vanishing: nab Val eq lam
-- statement:
--   The Wick Vanishing construction uses the nab Val eq lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean#L52-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean#L52-L61

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.nabVal_eq_lam {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (k : Type)
    [CommRing k] [Algebra ℚ k] [Algebra R k] [Nontrivial k] (B : FB R d O) (h : PS k 2 d) (w0 : O) (m : ℕ)
    (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (Q : MvPolynomial ι k) :
    B.nabVal k h w0 m f u Q = lam (fun e => B.nabVal k h w0 m f u (monomial e 1)) Q := by sorry
