-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P35_mixture_convexity_pure_reduction
-- name    : QAlgorithms.Papers.Independent.Advance50.P35.mixture_convexity_pure_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:43:56.12153+00:00
-- url     : https://prove2.me/theorems/31c06527-327d-4a36-8d56-1ab506f80a29
-- title:
--   Mixture convexity and pure reduction on the same registers
-- statement:
--   Let $\Phi=\{\phi_x,p_x\}_{x=0}^{k-1}$ be a finite nonempty ensemble of pairwise distinct CPTP channels on a common nonzero Hilbert space, with fixed nonnegative probabilities summing to one. Inputs are normalized positive trace-class operators on the full Hilbert spaces; the reference Hilbert space can be any nonzero Hilbert space. Use identical transmitters across different cells and arbitrary collective output measurements. All logarithms are base two and $0\log 0=0$. Fix $s\geq1$ and $r\geq0$. For any Borel probability law $\mu$ on normalized pure transmitters on these registers, with barycenter $\rho$,
--
--   $$\chi(\Phi\mid\rho)\leq\int\chi(\Phi\mid\psi)\,d\mu(\psi).$$
--
--   For every normalized transmitter $\rho$ there exists a normalized pure $\psi$ on the same registers satisfying $\chi(\Phi\mid\rho)\leq\chi(\Phi\mid\psi)$. Consequently the fixed-register supremum is unchanged by restricting to pure inputs. There is no energy constraint; the selected pure state need not preserve the energy of $\rho$. This is the reduction needed in the unconstrained optimization.
-- source:
--   Quantum Reading Capacity, arXiv:1107.3500v1, PDF p. 14, Appendix A.1: mixture convexity and pure-transmitter reduction

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P35

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsBarycenter tensorApply traceSize)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedRelativeEntropyNats binaryEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix coherentCoefficient)

open QAlgorithms.Papers.Independent.Support50.P20 (IsBinaryEffect)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Appendix A.1, PDF p.14, (A1)--(A5): mixture convexity and domination by
a pure transmitter on the SAME registers, with no energy constraint. -/
theorem mixture_convexity_pure_reduction {I A : Type} [Nonempty I] [Nonempty A]
    {k : ℕ} (M : Memory I k) (s r : ℕ) (hs : 1 ≤ s) :
    (∀ (rho : State (AssistedRegister I A s r))
      (mu : ProbabilityMeasure (PureState (AssistedRegister I A s r))),
      IsBarycenter (mu : Measure (PureState (AssistedRegister I A s r)))
        (fun psi => psi.val.coefficients) rho.coefficients →
      transmitterInformation M rho.coefficients ≤
        ∫⁻ psi, transmitterInformation M psi.val.coefficients
          ∂(mu : Measure (PureState (AssistedRegister I A s r)))) ∧
    (∀ rho : State (AssistedRegister I A s r), ∃ psi : PureState (AssistedRegister I A s r),
      transmitterInformation M rho.coefficients ≤ transmitterInformation M psi.val.coefficients) ∧
    (⨆ rho : State (AssistedRegister I A s r), transmitterInformation M rho.coefficients) =
      pureRegisterValue M A s r := by sorry

end QAlgorithms.Papers.Independent.Advance50.P35

end
