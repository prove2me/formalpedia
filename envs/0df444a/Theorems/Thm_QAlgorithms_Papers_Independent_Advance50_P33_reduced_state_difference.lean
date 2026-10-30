-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P33_reduced_state_difference
-- name    : QAlgorithms.Papers.Independent.Advance50.P33.reduced_state_difference
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:34:37.2214+00:00
-- url     : https://prove2.me/theorems/90a5ec5c-0d5e-491e-a029-d55026f22fc0
-- title:
--   The actual token partial traces and their explicit difference
-- statement:
--   Let $a\in\mathbb C\setminus\{0\}$ and let $|\chi_b(a)\rangle$ be the normalized two-mode encodings of Eq. (3), with token first and proof second. Construct $\rho_b$ by tracing out the proof. These operators are normalized positive trace-class densities; their number-basis environment sums converge absolutely. With $H=\rho_0-\rho_1$,
--   $$
--   H=\frac{e^{4|a|^2}}{e^{8|a|^2}-1}
--   \left[|a\rangle\langle a|+|-a\rangle\langle-a|
--   -e^{2|a|^2}\bigl(|a\rangle\langle-a|+|-a\rangle\langle a|\bigr)\right].
--   $$
--   This is an operator identity on the full oscillator space. The reduced states are constructed from the encoding rather than introduced as unrelated variables with a hypothesized identity.
-- source:
--   Quantum bit commitment under Gaussian constraints, arXiv:1105.2140v2, PDF p. 6, IV, Eq.(13): explicit token-state difference

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P33

open Filter

open scoped BigOperators Topology

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock fockKet bipartiteKet coherentKet
   coherentCoefficient CoherentRealized displacement displacementMatrix
   DisplacementRealized HasFockMatrix operatorOfMatrix IsDensity IsTraceClass
   nuclearTraceNorm fockTrace)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, Eq.(13): constructed reduced operators ARE normalized trace-class
densities and ARE the actual partial traces. The numerator is exp(4|a|^2),
confirmed in the PDF; the environment series is explicitly summable. -/
theorem reduced_state_difference (a : ℂ) (ha : a ≠ 0) :
    CoherentRealized ∧
    (∀ b : Bool, IsDensity (tokenState a b) ∧ HasFockMatrix (tokenState a b) (tokenReducedMatrix a b) ∧
      ∀ m n : ℕ, Summable (fun k : ℕ => commitmentEncoding a b (m, k) * star (commitmentEncoding a b (n, k)))) ∧
    tokenDifference a =
      (Real.exp (4 * Complex.normSq a) / (Real.exp (8 * Complex.normSq a) - 1) : ℝ) •
        ((InnerProductSpace.rankOne ℂ (coherentKet a) (coherentKet a) +
          InnerProductSpace.rankOne ℂ (coherentKet (-a)) (coherentKet (-a))) -
          (Real.exp (2 * Complex.normSq a) : ℝ) •
            (InnerProductSpace.rankOne ℂ (coherentKet a) (coherentKet (-a)) +
              InnerProductSpace.rankOne ℂ (coherentKet (-a)) (coherentKet a))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P33

end
