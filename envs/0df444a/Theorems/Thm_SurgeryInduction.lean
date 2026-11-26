-- Prove2me | Theorems.Thm_SurgeryInduction
-- name    : SurgeryInduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:15.749505+00:00
-- url     : https://prove2.me/theorems/2ccc6154-71fa-450e-8b23-4c400a9a6012
-- title:
--   Surgery Induction: Surgery Induction
-- statement:
--   The surgery algorithm (paper.tex lines 975-1075), formalized as a single strong induction on a
--   termination measure rather than as the paper's explicit while-loop with counters: for `0 < ε < 1`,
--   `0 < δ`, `0 < n`, and a closed piecewise-geodesic curve `γ`, there exist `N ≥ 1` and closed
--   piecewise-geodesic curves `(g j)_{j<N}` decomposing `γ`'s current, with the total length bounded by
--   `surgeryPotential ε δ n γ.len (smallPieceCount γ δ)` and each `g j`'s Morrey norm at most
--   `4ε⁻¹+2n+10`. This is exactly the conclusion of paper Lemma 3.1 (`surgery-lem`), specialized to
--   `L := γ.len`, `m := smallPieceCount γ δ`, before the algorithm has run (see `SurgeryLem`, which
--   supplies `smallPieceCount γ δ = 0` and recovers the paper's literal bound).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryInduction.lean#L30-L136
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryInduction.lean#L30-L136

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsDeltaEpsN
import Definitions.Def_Tablet_IsLSI
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_CutTypeI
import Definitions.Def_Tablet_CutTypeII
import Definitions.Def_Tablet_FullBallLem
import Definitions.Def_Tablet_SurgeryStepTypeI
import Definitions.Def_Tablet_SurgeryStepTypeII
import Definitions.Def_Tablet_SurgeryInduction
import Theorems.Thm_CutTypeI
import Theorems.Thm_CutTypeII
import Theorems.Thm_FullBallLem
import Theorems.Thm_SurgeryStepTypeI
import Theorems.Thm_SurgeryStepTypeII

set_option autoImplicit false
open Set ENNReal

theorem SurgeryInduction {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (δ ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hn : 0 < n)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ surgeryPotential ε δ n γ.len (smallPieceCount γ δ) ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10)) := by sorry
