-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_dof_sig
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_sig
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:17.133616+00:00
-- url     : https://prove2.me/theorems/6cd07041-84ec-51a1-9bb6-ac38ded24cc2
-- title:
--   Nab: dof sig
-- statement:
--   The Nab construction uses the dof sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConstantCoeffAddFirstSecond.lean#L115-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConstantCoeffAddFirstSecond.lean#L115-L130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyPointZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffAddFirstSecond
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.dof_sig {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (u : Fin d → R) (i : Fin d) :
    Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) -
      C (∑ j, sg1 k h i j * algebraMap R k (u j)) ∈ Ig R k (Fin 1 × Fin d) := by sorry
