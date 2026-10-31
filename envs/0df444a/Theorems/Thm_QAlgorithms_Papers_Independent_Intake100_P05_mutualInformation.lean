-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P05_mutualInformation
-- name    : QAlgorithms.Papers.Independent.Intake100.P05.mutualInformation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:46:01.521132+00:00
-- url     : https://prove2.me/theorems/2cb904dd-e35b-487e-b733-8afe8f03c9a0
-- title:
--   Selected-quadrature mutual information in bits
-- statement:
--   Let $V\ge1$, $0<T\le1$, $\chi_C\ge(1-T)/T$ and $\chi_D\ge0$ be finite. The detector noise $\chi_D$ is trusted and referred to Bob's received signal. After the public basis announcement, retain only the matching quadrature. Its joint classical law is that of $a\sim G_{V-1/V}$ and $b=\sqrt{T}\,a+n$, where $n$ is independent and Gaussian with variance $T(1/V+\chi_C)+\chi_D$. Write $P_{ab}$ for this law, and define mutual information in bits by $I(a:b)=D(P_{ab}\Vert P_a\otimes P_b)/\ln2$. It is finite, and with $\chi=\chi_C+\chi_D/T$,
--
--   $$
--   I(a:b)=\frac12\log_2\!\left(\frac{V+\chi}{\chi+1/V}\right).
--   $$
--
--   The normalization is per retained quadrature sample. For the original heterodyne implementation $\chi_D=1$; no second quadrature or homodyne sifting factor is counted. At $V=1$ Alice's datum is deterministic and the information is zero. The identity evaluates classical information and asserts no channel capacity.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, PDF p. 3, Eq.(4)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:0806.3954v2, PDF p.3, Eq.(4): exact classical information
per retained quadrature sample with trusted Bob-referred noise chiD.
There is no second heterodyne component or homodyne sifting factor here.
At V=1 Alice is deterministic and both sides of the information identity vanish. -/
theorem mutualInformation (V T chiC chiD : ℝ) (hV : 1 ≤ V)
    (hT : 0 < T) (hTupper : T ≤ 1) (hC : (1 - T) / T ≤ chiC)
    (hD : 0 ≤ chiD) :
    IsProbabilityMeasure (keyJointLaw V T chiC chiD) ∧
    mutualInformationBits (keyJointLaw V T chiC chiD) < ⊤ ∧
    mutualInformationBits (keyJointLaw V T chiC chiD) =
      ENNReal.ofReal ((1 / 2 : ℝ) *
        (Real.log ((V + (chiC + chiD / T)) /
          ((chiC + chiD / T) + 1 / V)) / Real.log 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P05

end
