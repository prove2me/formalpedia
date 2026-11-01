-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_rate_of_polarization_forward
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.rate_of_polarization_forward
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:55:54.818474+00:00
-- url     : https://prove2.me/theorems/e2900005-345b-478f-abae-149b680401d6
-- title:
--   Forward rate of polarization: small sum of root fidelities
-- statement:
--   Let $W$ be a binary-input classical–quantum channel with normalized density outputs and uniform-prior Holevo information $I(W)>0$, in bits. Fix real constants $R<I(W)$ and $\beta<1/2$. For every $N=2^n$, form the split channels $W_N^{(i)}$ using the actual polar encoder, the exposed classical history, and uniform future bits. There exists a sequence of information sets $A_N\subseteq\{1,\ldots,N\}$ such that
--
--   $$|A_N|\ge NR\quad\hbox{for every }n\ge0,\qquad
--   \sum_{i\in A_N}\sqrt{F(W_N^{(i)})}=o\!\left(2^{-N^\beta}\right).$$
--
--   Here $F$ is squared fidelity and the asymptotic limit is $n\to\infty$. The sum, rather than its average or maximum, is controlled. The source allows negative $R$ and negative $\beta$; for negative $R$ the empty information set is admissible. This assertion supplies the reliability input for the coding theorem.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 5, Theorem 3 (Rate of Polarization), forward assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P14

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P13 (compression)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, forward clause, PDF p.5; proof p.9. The quantity is a SUM,
not an average or maximum. Negative R and beta are allowed as printed.
The cardinality condition holds at every blocklength, including N=1. -/
theorem rate_of_polarization_forward {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (hI : 0 < symmetricInformation W) (R beta : ℝ)
    (hR : ENNReal.ofReal R < symmetricInformation W) (hb : beta < 1 / 2) :
    ∃ A : (n : ℕ) → Finset (PolarWire n),
      (∀ n, (2 ^ n : ℕ) * R ≤ ((A n).card : ℝ)) ∧
      Asymptotics.IsLittleO atTop
        (fun n => ∑ i ∈ A n, Real.sqrt (squaredCqFidelity (splitChannel W n i)))
        (polarDecay beta 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
