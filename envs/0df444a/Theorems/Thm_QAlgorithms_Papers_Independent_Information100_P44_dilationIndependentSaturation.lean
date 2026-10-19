-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_dilationIndependentSaturation
-- name    : QAlgorithms.Papers.Independent.Information100.P44.dilationIndependentSaturation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:44:02.720739+00:00
-- url     : https://prove2.me/theorems/173e4cef-d0de-41e3-89c5-37629fd547d6
-- title:
--   Remark 1: channel-invariant saturation in every dilation
-- statement:
--   Let $\Phi$ be a finite-bath thermal operation on a nonzero finite system at real inverse temperature $\beta$. For basis labels with $E_i-E_j=E_r-E_s$, suppose $p(r|i)p(s|j)>0$ and
--   $$|\Phi(|i\rangle\langle j|)_{rs}|^2=p(r|i)p(s|j).$$
--   Then in every finite nonempty bath energy-preserving dilation of that same channel, the corresponding shell vectors $w_{r|i}$ and $w_{s|j}$ are complex-collinear. Although the vectors depend on the dilation, this saturation implication is channel-invariant.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 8, Remark 1: channel-invariant saturation in every dilation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.8, Remark 1: every dilation of a fixed channel has the same saturation implication. -/
theorem dilationIndependentSaturation {d : ℕ} (hd : 0 < d) (E : Fin d → ℝ)
    (beta : ℝ) (Phi : Map d) (hTO : IsFiniteThermal E beta Phi) (i j r s : Fin d)
    (hgap : E i - E j = E r - E s) (hpos : 0 < population Phi r i * population Phi s j)
    (hsat : ‖Phi (matrixUnit i j) r s‖ ^ 2 = population Phi r i * population Phi s j) :
    ∀ (b : ℕ) (D : ThermalDilation E beta b), (∀ X, thermalApply D X = Phi X) →
      Collinear (shellVector D r i) (shellVector D s j) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
