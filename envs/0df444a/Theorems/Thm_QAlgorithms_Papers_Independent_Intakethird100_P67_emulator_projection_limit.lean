-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_emulator_projection_limit
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.emulator_projection_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:06:43.980328+00:00
-- url     : https://prove2.me/theorems/1554bf40-5be7-4073-9fd2-c13047b9550c
-- title:
--   §III: general-input projection and conditional emulation
-- statement:
--   Let normalized pure samples, $K\ge2$, generate the full algebra on their span, and let $\Pi$ be its projector. Fix an anchor and an unknown unitary $U$. In Fig.2 take the reconstructed system on $b=0$ and the old system from the SWAP on $b=1$. Let $\mathcal F_{T,b}$ be these averaged subnormalized output branches. For every input density operator,
--
--   $$\lim_{T\to\infty}\|\mathcal F_{T,0}(\rho)-U\Pi\rho\Pi U^\dagger\|_1=0,\qquad\lim_{T\to\infty}\|\mathcal F_{T,1}(\rho)-(I-\Pi)\rho(I-\Pi)\|_1=0.$$
--
--   This states projection followed by conditional emulation on the successful branch, including zero Born probability without division. The circuit and its algebra promise differ from Appendix H's unknown-projector instrument.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 4, §III: general-input projection and conditional emulation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.4,6: general-input Fig.2 instrument converges to conditional emulation
on H_in and projection on its complement, using the actual outcome-dependent wires. -/
theorem emulator_projection_limit (phi : K → EuclideanSpace ℂ I) (a : K)
    (hK : 2 ≤ Fintype.card K) (hphi : ∀ k, IsState (phi k))
    (hgen : Generates (pureSamples phi)) (U : Matrix.unitaryGroup I ℂ)
    (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) :
    let Pi := samplePi (pureSamples phi)
    Tendsto (fun T : ℕ => traceNorm (wireBranch phi a (U : Matrix I I ℂ) T false rho -
      densityConjugation (U : Matrix I I ℂ) (Pi * rho * Pi))) atTop (nhds 0) ∧
    Tendsto (fun T : ℕ => traceNorm (wireBranch phi a (U : Matrix I I ℂ) T true rho -
      (1-Pi) * rho * (1-Pi))) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
