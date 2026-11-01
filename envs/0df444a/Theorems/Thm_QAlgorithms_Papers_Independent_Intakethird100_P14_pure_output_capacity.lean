-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_pure_output_capacity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.pure_output_capacity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:01:56.214431+00:00
-- url     : https://prove2.me/theorems/9835e036-8823-4e73-84ea-698432768f16
-- title:
--   Binary pure-output channels attain their full classical capacity
-- statement:
--   Let $W:b\mapsto|\psi_b\rangle\langle\psi_b|$ be a fixed binary-input classical–quantum channel, where $\psi_0,\psi_1$ are unit vectors in a common complex Hilbert space. Define $C(W)$ independently as the supremum of asymptotically achievable nonnegative classical rates, using finite-message encoders, actual collective output POVMs, uniform-message error tending to zero, and all sufficiently large positive blocklengths. Let $I(W)$ be the uniform-prior Holevo information in bits. Then
--
--   $$C(W)=I(W).$$
--
--   For every $0\le R<C(W)$ there is a family of polar-rule information sets $A_N$, $|A_N|=\lfloor NR\rfloor$, such that the prescribed successive cancellation decoder has
--
--   $$P_e(N,\lfloor NR\rfloor,A_N)=o\!\left(2^{-N^\beta/2}\right)\quad\text{for every real }\beta<1/2,\qquad N=2^n\to\infty.$$
--
--   The capacity identity is explicitly attributed by the source to [15], and its optical application to [42]. The physical output space may be infinite, since the two pure states have a joint span of dimension at most two. This conclusion concerns the fixed binary alphabet, including a BPSK example, and does not identify unrestricted bosonic or signed resource-tradeoff capacity regions.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 9, Unnumbered conclusion: binary pure-output cq channels attain their full capacity

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

/-- Unnumbered conclusion, PDF pp.9–10, citing [15] (Guha) for the binary
pure-output capacity identity and [42] (Guha–Wilde) for the optical application.
Capacity is defined independently by actual POVM block codes. The fixed binary
cq alphabet may live in an infinite physical Hilbert space; its two pure
vectors span at most two dimensions. This is not a full-Fock energy-constrained
or resource-tradeoff region. Polar attainment includes the prescribed decoder
and its uniform-frozen-ensemble stretched-exponential error guarantee. -/
theorem pure_output_capacity {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (hpure : PureOutputs W) :
    binaryOperationalCapacity W = symmetricInformation W ∧
    ∀ R : ℝ, 0 ≤ R → ENNReal.ofReal R < binaryOperationalCapacity W → PolarAchieves W R := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
