-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P06_g_difference_monotone
-- name    : QAlgorithms.Papers.Independent.Support50.P06.g_difference_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:31:52.21621+00:00
-- url     : https://prove2.me/theorems/cd67b03d-0db3-43b2-b9d5-03315126a887
-- title:
--   Monotonicity of the thermal entropy difference
-- statement:
--   Let $g(x)=(x+1)\ln(x+1)-x\ln x$, with $0\ln0=0$. For a fixed real $c$ with $0\le c<1$,
--
--   $$0\le x\le y\quad\Longrightarrow\quad g(x)-g(cx)\le g(y)-g(cy).$$
--
--   The closed domain includes $x=0$ and the parameter includes $c=0$. This is the nondecrease used to choose the upper endpoint in equation (12).
-- source:
--   Capacity of the Bosonic Wiretap Channel and the Entropy Photon-Number Inequality, arXiv:0801.0841v1, PDF p. 3, §III, scalar monotonicity used in (12)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P06

open MeasureTheory Filter

open scoped ENNReal BigOperators Topology

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel identicalThermalKernel vacuum productCoherentKernel
   jointMix bobMarginal charlieMarginal pureLoss broadcast mixedOutput
   spectralEntropyNats FockPOVM realFockTracePair modeEnergy complexNormal
   StrongConjecture2)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, after (12): nondecrease on the entire closed nonnegative ray,
including c=0 and x=0. No derivative at zero is assumed. -/
theorem g_difference_monotone (c : ℝ) (hc : 0 ≤ c) (hc_one : c < 1) :
    MonotoneOn (fun x : ℝ => g x - g (c * x)) (Set.Ici 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P06

end
