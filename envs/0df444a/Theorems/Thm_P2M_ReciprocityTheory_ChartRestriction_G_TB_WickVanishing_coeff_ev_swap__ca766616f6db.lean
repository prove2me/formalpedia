-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap__ca766616f6db
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap__ca766616f6db
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:54:03.493802+00:00
-- url     : https://prove2.me/theorems/24342e1f-136a-44bb-904e-d3ee4d4d6d97
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing coeff ev swap  ca766616f6db: P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing coeff ev swap  ca766616f6db
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing coeff ev swap  ca766616f6db construction uses the P2 M Reciprocity Theory Chart Restriction G TB Wick Vanishing coeff ev swap  ca766616f6db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L174-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GaugeBilinearTermEqNegDoubleSum.lean#L174-L182

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] {d : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap__ca766616f6db (h : PS k 2 d) (m : Fin 2 × Fin d →₀ ℕ) :
    coeff m (ev (n := 2) ![pt k d 1, pt k d 0] h) = coeff (embDomain (swE d) m) h := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«WickVanishing».«coeff_ev_swap'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_coeff_ev_swap__ca766616f6db
