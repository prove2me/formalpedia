-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_oscillator_entropy_maximum
-- name    : QAlgorithms.Papers.Independent.Support50.P18.oscillator_entropy_maximum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:19:46.112871+00:00
-- url     : https://prove2.me/theorems/230f1ad0-7e92-4231-b8d1-224d6f5284cc
-- title:
--   Section 4.2: exact oscillator entropy maximum and upper bound (23)
-- statement:
--   Let $\ell\ge1$, $\hbar>0$, and $\omega_i>0$ be the parameters of the $\ell$-mode quantum oscillator on its full Fock space. Write $u_i=\hbar\omega_i$, $E_0=\frac12\sum_i u_i$, $E_*=(\prod_i u_i)^{1/\ell}$, and $g(x)=(1+x)h_2(x/(1+x))$, where $h_2$ is binary entropy in nats. For $E\ge E_0$, let $F_H(E)$ be the supremum of von Neumann entropy over all normalized states with mean energy at most $E$. Then
--
--   $$F_H(E)=\max_{\substack{\sum_i e_i=E\\ e_i\ge u_i/2}}\sum_{i=1}^{\ell}g(e_i/u_i-1/2)\le\ell\log\frac{E+E_0}{\ell E_*}+\ell.$$
--
--   The maximum is attained. This gives both the exact allocation formula and the explicit entropy majorant, including the ground-energy budget.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 9, Section 4.2

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

/-- Section 4.2, PDF p.9: exact attained allocation maximum and bound (23).
E=E0 is included. The undefined epsilon-sharp qualifier is separately deferred. -/
theorem oscillator_entropy_maximum {ell : ℕ} (O : OscillatorParameters ell) (E : ℝ)
    (hE : O.ground ≤ E) :
    (∃ e ∈ O.allocations E,
      O.entropyMaximum E = ENNReal.ofReal (O.allocationEntropy e) ∧
      ∀ v ∈ O.allocations E, O.allocationEntropy v ≤ O.allocationEntropy e) ∧
    O.entropyMaximum E ≤ ENNReal.ofReal (O.entropyUpper E) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
