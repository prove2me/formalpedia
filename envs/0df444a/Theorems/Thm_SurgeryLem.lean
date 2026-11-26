-- Prove2me | Theorems.Thm_SurgeryLem
-- name    : SurgeryLem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:30:19.86567+00:00
-- url     : https://prove2.me/theorems/25fbfcc9-9883-5685-9035-34a6ed843179
-- title:
--   Surgery Lem: Surgery Lem
-- statement:
--   Paper Lemma 3.1 (`surgery-lem`, paper.tex lines 597-621), with the paper's literal length
--   factor `(1 + 2ε/(1-ε) + 12ε⁻¹/(n(1-ε))) * γ.len` and Morrey bound `4ε⁻¹+2n+10`, recovered from
--   `SurgeryInduction` (the algorithm's conclusion before it has run, at a starting scale `δ` supplied
--   by `InitialDeltaExists` with `smallPieceCount γ δ = 0`), plus a direct degenerate-length argument
--   when `γ.len = 0` (where `InitialDeltaExists` does not apply). `δ` does not appear in the
--   statement: it is existentially consumed inside the proof, exactly as in the paper.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryLem.lean#L23-L60
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryLem.lean#L23-L60

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_surgeryPotential
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_InitialDeltaExists
import Definitions.Def_Tablet_SurgeryInduction
import Definitions.Def_Tablet_SurgeryLem
import Theorems.Thm_InitialDeltaExists
import Theorems.Thm_SurgeryInduction

set_option autoImplicit false
open Set ENNReal

theorem SurgeryLem {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (ε : ℝ) (n : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hn : 0 < n)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + 2 * ε / (1 - ε) + 12 * ε⁻¹ / ((n : ℝ) * (1 - ε))) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (4 * ε⁻¹ + 2 * n + 10)) := by sorry
