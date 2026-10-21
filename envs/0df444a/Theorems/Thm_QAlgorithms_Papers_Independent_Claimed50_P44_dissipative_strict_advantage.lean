-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_dissipative_strict_advantage
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.dissipative_strict_advantage
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:06:14.325564+00:00
-- url     : https://prove2.me/theorems/270d1e49-065a-49fc-b7a3-219265625181
-- title:
--   Dissipative Gaussian preprocessing strictly beats every Bob symplectic unitary
-- statement:
--   Consider the unity-gain Braunstein–Kimble protocol with ideal balanced-beam-splitter homodyne detection. The centered resource has blocks $A=\cosh(2r)I$, $B=(\cosh(2r)+1/2)I$ and $C=\operatorname{diag}(-\sinh(2r),\sinh(2r))$, with vacuum covariance $I$. There exists a squeezing parameter
--
--   $$0<r<-\tfrac12\log(3/4)$$
--
--   for which the deterministic vacuum attenuation channel on Bob with amplitude transmittance $t=\sinh(2r)/(\cosh(2r)-1/2)$ and added noise $(1-t^2)I$ has coherent-input fidelity strictly above $1/2$. Every Bob symplectic unitary, including any additional displacement, has fidelity strictly below $1/2$ and hence strictly below that of this channel. These comparisons hold for every input coherent displacement.
--
--   This gives an explicit operational witness for the abstract's strict advantage claim.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 1, Abstract; §IV, Fig.1, pp.6–7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.1 abstract and pp.6-7, Fig.1: explicit dissipative advantage over
EVERY Bob symplectic unitary. The sufficient open interval excludes r=0. -/
theorem dissipative_strict_advantage :
    ∃ r : ℝ, 0 < r ∧ r < -Real.log (3 / 4) / 2 ∧
      let t := dampingGain r
      let W := exampleOutput r (t • (1 : QuadratureMatrix)) (dampingNoise r) 0
      PhysicalResource (exampleResource r) ∧ GaussianCP (t • (1 : QuadratureMatrix)) (dampingNoise r) ∧
      t < 1 ∧ ∀ mean : PhasePoint, 1 / 2 < bellAverageFidelity 1 mean W ∧
        ∀ (S : QuadratureMatrix) (d : PhasePoint), Symplectic S →
          bellAverageFidelity 1 mean (exampleOutput r S 0 d) < 1 / 2 ∧
          bellAverageFidelity 1 mean (exampleOutput r S 0 d) < bellAverageFidelity 1 mean W := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
