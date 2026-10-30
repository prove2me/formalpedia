-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P50_transverseForwardEfficiency_maximum
-- name    : QAlgorithms.Papers.Independent.Extend50.P50.transverseForwardEfficiency_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:26:59.266629+00:00
-- url     : https://prove2.me/theorems/f14577ab-c09f-4b8e-964b-f431238e3970
-- title:
--   Transverse forward recall: the displayed efficiency model has maximum 4 exp(-2)
-- statement:
--   Let $d=\alpha L\ge 0$ be the dimensionless optical depth in the transverse-broadening forward-recall model, and define $\varepsilon_f^{(t)}(d)=d^2e^{-d}$. Then
--
--   $$
--   \bigl(\forall d\ge 0,\ \varepsilon_f^{(t)}(d)\le 4e^{-2}\bigr)
--   \quad\text{and}\quad
--   \varepsilon_f^{(t)}(2)=4e^{-2}.
--   $$
--
--   This is the attained maximum of the displayed scalar model. The paper rounds its value to 54 percent. It supplies neither a uniqueness assertion nor a universal bound across different memory protocols.
-- source:
--   Optical quantum memory, arXiv:1002.4659v3, PDF p. 7, II.D.2, unnumbered forward-recall display

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P50

namespace QAlgorithms.Papers.Independent.Extend50.P50

/-- PDF p.7, II.D.2: the displayed efficiency model attains its global maximum
at optical depth 2. The source's 54 percent is rounded; the exact value from
the display is `4 * Real.exp (-2)`. This does not add a uniqueness claim. -/
theorem transverseForwardEfficiency_maximum :
    (∀ d : ℝ, 0 ≤ d → transverseForwardEfficiency d ≤ 4 * Real.exp (-2)) ∧
    transverseForwardEfficiency 2 = 4 * Real.exp (-2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P50
