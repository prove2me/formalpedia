-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_thermalEntropyTightness
-- name    : QAlgorithms.Papers.Independent.Next46.P13.thermalEntropyTightness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:12:04.560499+00:00
-- url     : https://prove2.me/theorems/43652f56-bfc0-43df-8a07-22cfd5415dc7
-- title:
--   Appendix C: sharpness of the entropy isoperimetric constant
-- statement:
--   Let $\omega_n$ be the one-mode thermal state with real occupation $n>0$. Let $J$ be the displacement-relative-entropy Fisher information in the Weyl normalization $W(v)=\exp(i\sqrt{2\pi}\,v\cdot\sigma R)$, and let $N(\rho)=\exp S(\rho)$ in one mode. Then
--
--   $$J(\omega_n)=4\pi\log\frac{n+1}{n},\qquad
--   N(\omega_n)=\frac{(n+1)^{n+1}}{n^n},$$
--   $$J(\omega_n)N(\omega_n)=4\pi\left(\frac{n+1}{n}\right)^n
--   \log\left[\left(\frac{n+1}{n}\right)^{n+1}\right]
--   \longrightarrow4\pi e\quad(n\to+\infty).$$
--
--   The powers are real powers, and the logarithm encloses the entire power $n+1$. This certifies asymptotic sharpness, not equality at finite occupation. Finiteness of entropy and the local displacement Hessian are included.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 31, Appendix C

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF p.31, Appendix C: the logarithm encloses the full real power n+1.
Sharpness is only asymptotic, with no equality claimed at finite n. -/
theorem thermalEntropyTightness :
    (∀ n : ℝ, 0 < n →
      B.ThermalRealized (2 * n + 1) ∧ C.fockEntropyNats (C.photonMeanThermalState n) ≠ ⊤ ∧
      FiniteDisplacementC2 (C.photonMeanThermalState n) ∧
      fisher (C.photonMeanThermalState n) = 4 * Real.pi * Real.log ((n + 1) / n) ∧
      thermalEntropyPower (C.photonMeanThermalState n) = Real.rpow (n + 1) (n + 1) / Real.rpow n n ∧
      fisher (C.photonMeanThermalState n) * thermalEntropyPower (C.photonMeanThermalState n) =
        4 * Real.pi * Real.rpow ((n + 1) / n) n *
          Real.log (Real.rpow ((n + 1) / n) (n + 1))) ∧
    Tendsto (fun n : ℝ => fisher (C.photonMeanThermalState n) * thermalEntropyPower (C.photonMeanThermalState n))
      atTop (nhds (4 * Real.pi * Real.exp 1)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
