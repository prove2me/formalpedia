-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_projective_measurement_limit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.projective_measurement_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:04:53.667057+00:00
-- url     : https://prove2.me/theorems/82dbe070-9f9a-413a-825e-c74dcf47691e
-- title:
--   Appendix H1–H2: asymptotic projective instrument
-- statement:
--   For an arbitrary finite nonempty normalized sample family, let $\Pi$ project onto its span and let $\mathcal E_{T,0},\mathcal E_{T,1}$ be the actual subnormalized branches of the Fig.7 instrument with ideal controlled reflections. For every input density operator,
--
--   $$\lim_{T\to\infty}\|\mathcal E_{T,0}(\rho)-\Pi\rho\Pi\|_1=0,\qquad\lim_{T\to\infty}\|\mathcal E_{T,1}(\rho)-(I-\Pi)\rho(I-\Pi)\|_1=0.$$
--
--   Thus the limiting outcome probabilities and conditional states are those of the projective measurement. Subnormalized branches remain defined when a Born probability is zero; no normalization of an impossible conditioned event or new diamond-norm rate is asserted.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 32, Appendix H1–H2: asymptotic projective instrument

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.31–32: convergence to the two subnormalized projective branches, including
zero Born probability, with b=0 for span detection and b=1 for its complement. -/
theorem projective_measurement_limit [Nonempty K] (phi : K → EuclideanSpace ℂ I)
    (hphi : ∀ k, IsState (phi k)) (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    let Pi := samplePi (pureSamples phi)
    Tendsto (fun T : ℕ => traceNorm (projectionBranch phi T false rho - Pi * rho * Pi)) atTop (nhds 0) ∧
    Tendsto (fun T : ℕ => traceNorm (projectionBranch phi T true rho -
      (1-Pi) * rho * (1-Pi))) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
