-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_highEnergyDispersionRatio
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.highEnergyDispersionRatio
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T07:52:00.74317+00:00
-- url     : https://prove2.me/theorems/56fd141b-9231-4507-b621-6df68d87bab6
-- title:
--   High-energy agreement of dispersion ratios
-- statement:
--   For received photon number $x>0$, let $v(x)=x(x+1)[\log_2(x+1)-\log_2x]^2$ and $v_{\rm Het}(x)=x(x+2)(\log_2e)^2/(x+1)^2$. Then
--
--   $$
--   \lim_{x\to+\infty}\frac{v(x)}{v_{\rm Het}(x)}=1.
--   $$
--
--   Both dispersions are in bits squared. The comparison concerns their high-energy ratio; it makes no claim that a capacity difference tends to zero.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 12, §6.2, (6.12)–(6.13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.11–12, (6.12)–(6.13): high-energy ratio of dispersions, both in
bits squared. No absolute agreement of the two capacities is asserted. -/
theorem highEnergyDispersionRatio :
    Tendsto (fun x : ℝ => thermalDispersion x / heterodyneDispersion x)
      atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
