-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_channel_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.channel_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:21:35.571201+00:00
-- url     : https://prove2.me/theorems/2dac92de-3c9d-4795-abc1-8ed324d2699c
-- title:
--   Optimal channel tomography and attaining corrected seed
-- statement:
--   For common dimension $d\ge1$, prior mean Choi matrix $I/d$, and identity Hilbert–Schmidt representation, every physical tester and finite-loss unbiased dual reconstructing the complex channel span satisfies
--
--   $$\eta_{\mathcal C}\ge d^6+(2\sqrt2-3)d^4+(5-4\sqrt2)d^2+2(\sqrt2-1).$$
--
--   The bound is attained by the $SU(d)\times SU(d)$ orbit of $\Pi_0=d|\Psi\rangle\!\rangle\langle\!\langle\Psi|$, where $\Psi=\sqrt{(1-\beta)I/d+\beta|\psi\rangle\langle\psi|}$, $\|\psi\|=1$, and $\beta=\sqrt{(d+1)/(2+\sqrt2(d^2-1))}$. It has an attaining dual and a frame complete on the channel span, and is physically measured with density $d\Pi$ after normalized maximally entangled channel input. For $d\ge2$ its coefficient is $A=1/(2+\sqrt2(d^2-1))$; the scalar minimum at $d=1$ is $1$. This is a global setup-and-dual optimum.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (34), second line; (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, (34) second line, and p.4: global channel minimum and attaining corrected seed.
Printed after (36): beta_C=[(d-1)(2+sqrt(2)(d²-1))]^(-1/2).
Changed to sqrt((d+1)/(2+sqrt(2)(d²-1))), since (29),(36) give
A=beta²/(d+1) and the channel optimizer below (33) is 1/(2+sqrt(2)(d²-1)). -/
theorem channel_optimum {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) :
    (∀ (X : Type) [MeasurableSpace X] (mu : Measure X) [SFinite mu]
      (P D : X → Op (ChoiBasis d)), TomographyAdmissible mu P D .channels →
      (d : ℝ)^6 + (2 * Real.sqrt 2 - 3) * (d : ℝ)^4 +
        (5 - 4 * Real.sqrt 2) * (d : ℝ)^2 + 2 * (Real.sqrt 2 - 1) ≤ eta .channels mu P D) ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), QAlgorithms.IsState psi → Attains haar .channels psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
