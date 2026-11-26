-- Prove2me | Theorems.Thm_SurgeryEta
-- name    : SurgeryEta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:50.92768+00:00
-- url     : https://prove2.me/theorems/91077254-755b-5f91-9351-4f58289db6ce
-- title:
--   Surgery Eta: Surgery Eta
-- statement:
--   Paper Cor. 3.2 (`surgery-eta`, paper.tex lines 628-654), with the universal constant `C'`
--   pinned to the numeral `522` and the paper's `ε = cη`, `n = ⌈ε⁻²⌉` prescription pinned to `c = 1/15`
--   (sharp at `η = 1`), obtained from `SurgeryLem` at `ε := η/15`, `n := ⌈ε⁻²⌉`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryEta.lean#L17-L80
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/SurgeryEta.lean#L17-L80

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_Curve
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_curveMeasure
import Definitions.Def_Tablet_SurgeryLem
import Definitions.Def_Tablet_SurgeryEta
import Theorems.Thm_SurgeryLem

set_option autoImplicit false
open Set ENNReal

theorem SurgeryEta {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (GP : GeodesicPairing E) (γ : Curve E) (η : ℝ)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) :
    ∃ (N : ℕ) (g : Fin N → Curve E), 0 < N ∧
      (∀ j, IsClosedCurve (g j)) ∧ (∀ j, IsPiecewiseGeodesic (g j)) ∧
      (∀ ω : Form1 E, curveCurrent γ ω = ∑ j, curveCurrent (g j) ω) ∧
      (∑ j, (g j).len) ≤ (1 + η) * γ.len ∧
      (∀ j, morreyNorm (curveMeasure (g j)) ≤ ENNReal.ofReal (522 / η ^ 2)) := by sorry
