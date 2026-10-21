-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_minimum_entropy_fixed_sequence_epr
-- name    : QAlgorithms.Papers.Independent.Next46.P45.minimum_entropy_fixed_sequence_epr
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:49:01.22221+00:00
-- url     : https://prove2.me/theorems/490cd457-1a64-4d1c-a659-9d04d289b451
-- title:
--   Minimum sequence entropy at fixed EPR functional
-- statement:
--   Let $0<\Delta<1$ and $c\in\mathcal C$, where $\mathcal C$ consists of real nonnegative nonincreasing sequences with $\sum_Nc_N^2=1$. Put $\delta(c)=\sum_{N\ge0}(N+1)(c_N-c_{N+1})^2$ and $e(c)=-\sum_{N\ge0}c_N^2\log_2(c_N^2)\in[0,+\infty]$, with $0\log_2 0=0$. Set $r_\Delta=-\frac12\ln\Delta$ and $c_N^\Delta=\tanh(r_\Delta)^N/\cosh(r_\Delta)$. If $\delta(c)=\Delta$, then $c^\Delta\in\mathcal C$, $\delta(c^\Delta)=\Delta$, and
--
--   $$e(c)\ge e(c^\Delta)=E\bigl(\Psi_s(r_\Delta)\bigr).$$
--
--   Moreover, $c^\Delta$ is the unique geometric sequence in $\mathcal C$ with EPR functional $\Delta$: among sequences $b_N=a q^N$ with $a>0$ and $0\le q<1$, the constraints force $b=c^\Delta$. This is the scalar minimization underlying the pure-state entanglement bound; uniqueness of arbitrary entropy minimizers is not asserted.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 3, Lemma 2: minimum entropy for fixed Schmidt-sequence EPR functional

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.3, Lemma 2; (1),(3),(4), pp.1–2 fix the geometric parameter.
Printed: c_N^Delta proportional to exp(-N r_Delta). Changed: tanh(r_Delta)^N/cosh(r_Delta).
Why: the printed parameter contradicts (1),(3),(4) and the asserted entropy identity;
the proof uses a different Lagrange-multiplier parameter. Independent moderation pending. -/
theorem minimum_entropy_fixed_sequence_epr
    (delta : ℝ) (hdelta : 0 < delta) (hlt : delta < 1)
    (c : ℕ → ℝ) (hc : SchmidtClass c)
    (hlevel : sequenceUncertainty c = ENNReal.ofReal delta) :
    SchmidtClass (geometricCoefficients delta) ∧
    IsGeometric (geometricCoefficients delta) ∧
    sequenceUncertainty (geometricCoefficients delta) = ENNReal.ofReal delta ∧
    sequenceEntropy (geometricCoefficients delta) =
      pureEntanglement (squeezedVector (squeezingAt delta)) ∧
    sequenceEntropy (geometricCoefficients delta) ≤ sequenceEntropy c ∧
    (∀ b : ℕ → ℝ, SchmidtClass b → IsGeometric b →
      sequenceUncertainty b = ENNReal.ofReal delta → b = geometricCoefficients delta) := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
