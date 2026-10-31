-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_partialDual_trace
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.partialDual_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:45:01.218705+00:00
-- url     : https://prove2.me/theorems/39c78b50-c54a-4072-939c-2d83d4347366
-- title:
--   Generalized trace duality
-- statement:
--   Let $\mathcal H,\mathcal K$ be complex separable complete Hilbert spaces and $\rho$ a nonzero bounded PSD operator on $\mathcal H$. Positive traces may be infinite.
--
--   Let $\Phi:\mathcal B(\mathcal K)\to\mathcal B(\mathcal H)$ be normal, unital and completely positive. Its countable Kraus representation is $\Phi(A)=\sum_i V_i^* A V_i$, in the strong operator topology. The partial dual $\Phi^*(B)=\sum_i V_i B V_i^*$ is defined on a positive bounded $B$ precisely when this strong sum is bounded. If $\Phi^*$ is defined on nonzero bounded PSD $\rho$, then for every nonzero bounded PSD $A$ on $\mathcal K$, $$\operatorname{Tr}[A^{1/2}\Phi^*(\rho)A^{1/2}]=\operatorname{Tr}[\Phi(A)^{1/2}\rho\Phi(A)^{1/2}].$$ Both sides are extended positive traces; neither input needs to be trace class. This is generalized Heisenberg-Schrodinger trace duality.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 34, Lemma IV.11

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P49

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass TraceClass traceNormTopology)

open QAlgorithms.Papers.Independent.Bridge50.P48 (hilbertPositiveTrace)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Lemma IV.11, PDF p.34: both generalized traces are symmetric square-root
sandwiches. The test operator A is arbitrary nonzero PSD, not just an effect. -/
theorem partialDual_trace [TopologicalSpace.SeparableSpace H] [TopologicalSpace.SeparableSpace K]
    {I J : Type*} (b : HilbertBasis I ℂ H) (d : HilbertBasis J ℂ K)
    (rho : H →L[ℂ] H) (hrho : NonzeroPositive rho)
    (Phi : HeisenbergOperation H K) (hdefined : DualDefined Phi rho)
    (A : K →L[ℂ] K) (hA : NonzeroPositive A) :
    hilbertPositiveTrace d (positiveSpectralPower A (1 / 2) * partialDual Phi rho * positiveSpectralPower A (1 / 2)) =
      hilbertPositiveTrace b (positiveSpectralPower (Phi.map A) (1 / 2) * rho *
        positiveSpectralPower (Phi.map A) (1 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
