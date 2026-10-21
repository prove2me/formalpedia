-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_thermalFisherTightness
-- name    : QAlgorithms.Papers.Independent.Next46.P13.thermalFisherTightness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:11:17.360034+00:00
-- url     : https://prove2.me/theorems/229eab01-e14d-4097-a308-c1c19f3cb2b7
-- title:
--   Appendix B: thermal Fisher formula and sharpness of (40)
-- statement:
--   Let $\omega_n$ be the one-mode thermal state with real occupation $n>0$, and let $g(n)=(n+1)\log(n+1)-n\log n$. Use the canonical heat generator $L_{\rm heat}=-\pi([Q,[Q,\cdot]]+[P,[P,\cdot]])$. Define $J$ as the trace of the Hessian at zero of $v\mapsto D(\rho\Vert W(v)\rho W(v)^\dagger)$, where $W(v)=\exp(i\sqrt{2\pi}\,v\cdot\sigma R)$. Then $S(\omega_n)=g(n)$, $e^{tL_{\rm heat}}\omega_n=\omega_{n+2\pi t}$ for $t\ge0$, and
--
--   $$J(\omega_n)=4\pi\log\frac{n+1}{n},\qquad
--   J(e^{tL_{\rm heat}}\omega_n)=4\pi\log\left(1+\frac1{n+2\pi t}\right),$$
--   $$\left.\frac d{dt}\left[\frac12J(e^{tL_{\rm heat}}\omega_n)\right]^{-1}\right|_{0+}
--   =\frac1{n(n+1)[\log(1+1/n)]^2}\longrightarrow1\quad(n\to+\infty).$$
--
--   This gives asymptotic sharpness of the inverse-Fisher sensitivity constant. The statement establishes finite local twice continuous displacement differentiability on these thermal states, so $J$ denotes the actual Hessian.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 30, Appendix B, (77)–(78)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF pp.30–31, Appendix B, (77)–(78): complete thermal Fisher formulas and
asymptotic sharpness. The inverse is of the whole J/2, giving 2/J. -/
theorem thermalFisherTightness :
    (∀ n : ℝ, 0 < n →
      B.ThermalRealized (2 * n + 1) ∧ HasTrivialKernel (C.photonMeanThermalState n) ∧
      C.fockEntropyNats (C.photonMeanThermalState n) = ENNReal.ofReal (C.g n) ∧
      FiniteDisplacementC2 (C.photonMeanThermalState n) ∧
      fisher (C.photonMeanThermalState n) = 4 * Real.pi * Real.log ((n + 1) / n) ∧
      (∀ t : ℝ, 0 ≤ t → HeatOneRealized t (C.photonMeanThermalState n) ∧
        heatOne t (C.photonMeanThermalState n) = C.photonMeanThermalState (n + 2 * Real.pi * t) ∧
        FiniteDisplacementC2 (heatOne t (C.photonMeanThermalState n)) ∧
        fisher (heatOne t (C.photonMeanThermalState n)) =
          4 * Real.pi * Real.log (1 + 1 / (n + 2 * Real.pi * t))) ∧
      HasDerivWithinAt (fun t : ℝ => (fisher (heatOne t (C.photonMeanThermalState n)) / 2)⁻¹)
        (1 / (n * (n + 1) * Real.log (1 + 1 / n) ^ 2)) (Set.Ici 0) 0) ∧
    Tendsto (fun n : ℝ => derivWithin
      (fun t : ℝ => (fisher (heatOne t (C.photonMeanThermalState n)) / 2)⁻¹) (Set.Ici 0) 0)
      atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
