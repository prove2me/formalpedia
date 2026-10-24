-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_oscillator_continuity
-- name    : QAlgorithms.Papers.Independent.Support50.P18.oscillator_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:20:44.063217+00:00
-- url     : https://prove2.me/theorems/e2f19d64-0e94-42d5-88ce-9e1ca3264669
-- title:
--   Corollary 3: explicit oscillator continuity bound
-- statement:
--   Let $B$ be the oscillator described above, let $R$ be any complementary separable system, and let $f$ be a real function on states of $BR$ with finite mean $B$ energy. Suppose $a,b,c_-,c_+\ge0$ are fixed constants such that, for every pair in this domain and every $0<p<1$, its mixture defect lies between $-a h_2(p)$ and $b h_2(p)$, and $-c_-H(\rho_B)\le f(\rho)\le c_+H(\rho_B)$. For $E>E_0$, states with both marginal energies at most $E$, and $0<\varepsilon\le1/2$ with $\frac12\|\rho-\sigma\|_1\le\varepsilon$, one has
--
--   $$|f(\rho)-f(\sigma)|\le(c_-+c_+)\sqrt{2\varepsilon}\,\ell\left(\log\frac{E/\varepsilon+E_0}{\ell E_*}+1\right)+(a+b)g(\sqrt{2\varepsilon}).$$
--
--   For pure inputs the same bound holds with its parameter replaced by $\varepsilon^2/2$, under the original distance hypothesis. This is the explicit oscillator form of the marginal-entropy AFW bound.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 9, Corollary 3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P18

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P18

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState traceSize rankOne)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Renew46.P08
  (coefficientEnergy entropySupremum extendedHalfTraceDistance)

/-- Corollary 3, PDF p.9: (24) and its pure-state refinement under the original
hypothesis d(rho,sigma)≤eps; only the bound parameter becomes eps^2/2. -/
theorem oscillator_continuity {ell : ℕ} {R : Type} [Countable R] [Nonempty R]
    (O : OscillatorParameters ell) (C : AFWConstants)
    (f : Matrix ((Fin ell → ℕ) × R) ((Fin ell → ℕ) × R) ℂ → ℝ)
    (hf : O.EntropyControlled C f) (E : ℝ) (hE : O.ground < E) :
    ∀ (rho sigma : State ((Fin ell → ℕ) × R)) (eps : ℝ),
      O.meanEnergy (traceSecond rho.coefficients) ≤ ENNReal.ofReal E →
      O.meanEnergy (traceSecond sigma.coefficients) ≤ ENNReal.ofReal E →
      0 < eps → eps ≤ 1 / 2 → nuclearStateDistance rho sigma ≤ ENNReal.ofReal eps →
      |f rho.coefficients - f sigma.coefficients| ≤ O.continuityBound C E eps ∧
      ((∃ u : Hilbert ((Fin ell → ℕ) × R), ‖u‖ = 1 ∧ rho.coefficients = rankOne u) →
       (∃ u : Hilbert ((Fin ell → ℕ) × R), ‖u‖ = 1 ∧ sigma.coefficients = rankOne u) →
       |f rho.coefficients - f sigma.coefficients| ≤
         O.continuityBound C E (eps ^ 2 / 2)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
