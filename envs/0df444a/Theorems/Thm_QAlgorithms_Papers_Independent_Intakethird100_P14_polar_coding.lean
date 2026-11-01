-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P14_polar_coding
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P14.polar_coding
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:53:05.705002+00:00
-- url     : https://prove2.me/theorems/438034a2-9e34-4469-90d7-24e3b36e8661
-- title:
--   Polar coding: ensemble block error below the symmetric information rate
-- statement:
--   Let $W:b\mapsto\rho_b$ be a binary-input classical–quantum channel, with positive trace-one outputs on a common complex Hilbert space. Let $I(W)$ be its uniform-prior Holevo information in bits and let $F(W)$ be squared fidelity. Fix real numbers $0\le R<I(W)$ and $\beta<1/2$. For each $N=2^n$, choose any information set $A_N$ of cardinality $\lfloor NR\rfloor$ such that every included split channel has fidelity no larger than every excluded one. Encode by $x^N=u^NG_N$ and use the specified adaptive square-root-density successive cancellation decoder, with the frozen bits known to the receiver. Let $P_e(N,\lfloor NR\rfloor,A_N)$ average block error uniformly over both information messages and frozen vectors. Then
--
--   $$P_e(N,\lfloor NR\rfloor,A_N)=o\!\left(2^{-N^\beta/2}\right)\qquad(n\to\infty).$$
--
--   This holds for every family of information sets satisfying the polar rule, including all choices among ties. It is the paper’s coding guarantee at the symmetric information rate. The parameter $\beta$ need not be positive.
-- source:
--   Polar codes for classical-quantum channels, arXiv:1109.2591v3, PDF p. 6, Theorem 6 (Polar Coding Theorem); precise headline for the p.1 paper-result seed

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

/-- Theorem 6, PDF p.6; proof p.9. Uniform-message and frozen-ensemble
block error for every sequence of Definition 5 sets, including arbitrary ties.
The standing R>=0 is explicit; beta need not be positive. -/
theorem polar_coding {I : Type} (W : Bit → OutputCoefficients I) (hW : IsBinaryCqChannel W)
    (R beta : ℝ) (hR0 : 0 ≤ R) (hR : ENNReal.ofReal R < symmetricInformation W)
    (hb : beta < 1 / 2) (A : (n : ℕ) → Finset (PolarWire n))
    (hA : ∀ n, PolarRule W n R (A n)) :
    Asymptotics.IsLittleO atTop (fun n => ensembleError W n (A n))
      (polarDecay beta (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P14

end
