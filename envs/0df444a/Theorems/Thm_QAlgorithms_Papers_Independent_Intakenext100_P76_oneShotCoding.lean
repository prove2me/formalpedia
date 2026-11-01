-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P76_oneShotCoding
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P76.oneShotCoding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:48:07.377747+00:00
-- url     : https://prove2.me/theorems/da74bc5a-328b-48cc-bddf-afdee26818d9
-- title:
--   One-shot achievability for separable-output pure-state cq channels
-- statement:
--   Let $W:x\mapsto|\phi_x\rangle$ have normalized pure outputs on a separable complex Hilbert space. Let $\mu$ be any probability law on its measurable input alphabet, with the pure-state projector map measurable in the trace-norm Borel structure. Compute $\rho=\int |\phi_x\rangle\langle\phi_x|\,d\mu(x)$. For $0<\eta<\varepsilon<1$, define $H_s^a(\rho)=\sup\{\gamma:\operatorname{Tr}(\rho\{\rho\le 2^{-\gamma}I\})\ge1-a\}$. Then a finite deterministic code with $M\ge1$ equiprobable messages and one joint POVM satisfies
--
--   $$
--   P_{\rm err}\le\varepsilon,\qquad
--   \log_2M\ge H_s^{\varepsilon-\eta}(\rho)-\log_2\frac{4\varepsilon}{\eta^2}.
--   $$
--
--   The same lower bound holds for the extended supremum $\log_2M^*(W,\varepsilon)$ over all such finite codes. This is a one-shot achievability statement without an output-dimension or input-support cutoff.
-- source:
--   Second-order coding rates for pure-loss bosonic channels, arXiv:1408.5328v3, PDF p. 6, Theorem 3, (4.1)–(4.2)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P76

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Theorem 3, PDF p.6, (4.1)–(4.2), proof pp.6–8: one-shot coding on any
separable-output pure-state cq channel and any measurable input law. The spectral
law is a decomposition of the computed mean output, not an unrelated density.
Integer cardinalities are actual finite code witnesses; retain M-1 interference
terms when rounding. The decoder uses average error as in (3.15). -/
theorem oneShotCoding {X : Type*} {I : Type} [MeasurableSpace X] [Countable I]
    (W : X → I → ℂ) (mu : Measure X) [IsProbabilityMeasure mu]
    (hnorm : ∀ x, IsUnitCoefficientVector (W x))
    (hmeas : ∀ a b, Measurable (fun x => Matrix.vecMulVec (W x) (star (W x)) a b))
    (p : ℕ → ℝ) (hspec : HasSpectralLaw (meanOutput W mu) p)
    (epsilon slack : ℝ) (he : 0 < epsilon) (he1 : epsilon < 1)
    (hs : 0 < slack) (hse : slack < epsilon) :
    let R := spectralInfEntropy p (epsilon - slack) - logTwo (4 * epsilon / slack ^ 2)
    HasFiniteCode W epsilon R ∧ (R : EReal) ≤ logMaxCodeSize W epsilon := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P76

end
