-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_controlled_with_bridge
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.controlled_with_bridge
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:02:22.814427+00:00
-- url     : https://prove2.me/theorems/a2cf2ed7-0034-4855-b55c-d2a6b15b76fb
-- title:
--   Appendix G2, Eq.(G2): bridge samples enable controlled emulation
-- statement:
--   Let a finite nonempty mixed sample family generate all operators on $H_{\rm in}$. Take a unit vector $\phi\in H_{\rm in}$ and normalized control amplitudes $\alpha,\beta$ with both nonzero. In addition to tagged original samples, supply the pure bridge $|\Phi_{\rm in}\rangle=|\phi\rangle(\alpha|0\rangle+\beta|1\rangle)$ and its exact output $|\Phi_{\rm out}\rangle=U^c|\Phi_{\rm in}\rangle$. The augmented input family satisfies
--
--   $$\operatorname{Alg}_{\mathbb C}\!\left(\{\rho_k\otimes|b\rangle\langle b|:b=0,1\}\cup\{|\Phi_{\rm in}\rangle\langle\Phi_{\rm in}|\}\right)=\mathcal L(H_{\rm in}\otimes\mathbb C^2).$$
--
--   The actual mixed-sample emulator with this pure anchor consequently converges uniformly to controlled conjugation on supported input density operators. The bridge output supplies the relative phase; that phase is not inferred from the original density records.
--
--   The tagged output resources are $\rho_k^{\rm in}\otimes|0\rangle\langle0|$ and $\rho_k^{\rm out}\otimes|1\rangle\langle1|$, together with the output bridge; controlled $U$ leaves the zero-control branch unchanged.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 28, Appendix G2, Eq.(G2): bridge samples enable controlled emulation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.28, G2: nonzero control amplitudes in an additional pure bridge generate
the full systemControlled-space algebra and enable emulation by the actual mixed-sample channel.
Printed: the final output-record list uses both control projectors tensor S_out.
Changed: the constructed target-conjugated records use S_in on control zero and
S_out on control one, plus the given output bridge. Why: the defined controlled-U
acts as identity on control zero; these records are available from the given resources. -/
theorem controlled_with_bridge [Nonempty K] (S : K → Matrix I I ℂ)
    (hS : ∀ k, IsDensityMatrix (S k)) (hgen : Generates S)
    (phi : EuclideanSpace ℂ I) (hphi : IsState phi)
    (hsupport : InSampleSupport S (pureDensity phi)) (alpha beta : ℂ)
    (hnorm : ‖alpha‖ ^ 2 + ‖beta‖ ^ 2 = 1) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) :
    let B := bridgeSamples S phi alpha beta
    let bridge := tensorVec phi (WithLp.toLp 2 fun b => if b then beta else alpha)
    Generates B ∧ ∀ (U : Matrix.unitaryGroup I ℂ) (eps : ℝ), 0 < eps →
      ∃ N : ℕ, ∀ T ≥ N, ∀ rho : Matrix (I × Bool) (I × Bool) ℂ, IsDensityMatrix rho → InSampleSupport B rho →
        traceDistance (mixedEmulate B none bridge (systemControlled (U : Matrix I I ℂ)) T rho)
          (densityConjugation (systemControlled (U : Matrix I I ℂ)) rho) ≤ eps := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
