-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P18_entanglement_asymptotic_continuity
-- name    : QAlgorithms.Papers.Independent.Support50.P18.entanglement_asymptotic_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:25:36.238482+00:00
-- url     : https://prove2.me/theorems/8dfd94bf-0216-432b-b312-509a795d5f5b
-- title:
--   Corollary 5: asymptotic continuity of ER and its regularization
-- statement:
--   Let $A,B$ be infinite-dimensional separable systems, and suppose $H_A\ge0$ satisfies condition (22). Fix a finite budget $E\ge E_0$. For each positive integer $n$, let $\rho_n,\sigma_n$ be arbitrary states on $A^nB^n$, with no product-state assumption, such that both mean energies of the additive Hamiltonian $H_{A^n}=\sum_{j=1}^n H_A^{(j)}$ are at most $nE$. If $\|\rho_n-\sigma_n\|_1\to0$, all entanglement quantities below are finite and
--
--   $$\lim_{n\to\infty}\frac{|E_R(\rho_n)-E_R(\sigma_n)|}{n}=0,\qquad\lim_{n\to\infty}\frac{|E_R^\infty(\rho_n)-E_R^\infty(\sigma_n)|}{n}=0.$$
--
--   Here $E_R$ and $E_R^\infty$ have their actual relative-entropy and regularized meanings. This applies in particular to oscillator Hamiltonians, which satisfy (22). The formal indexing uses $n+1$ to range over exactly the positive block lengths.
-- source:
--   Adaptation of the Alicki-Fannes-Winter method for the set of states with bounded energy and its use, arXiv:1609.07044v5, PDF p. 16, Corollary 5

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

/-- Corollary 5, PDF p.16: arbitrary correlated block states, indexed by n+1
so that every quotient has positive denominator. The per-copy energy budget
is fixed and neither input sequence is required to consist of tensor powers. -/
theorem entanglement_asymptotic_continuity {I J : Type}
    [Countable I] [Infinite I] [Countable J] [Infinite J]
    (energy : I → ℝ≥0) (h22 : Condition22 energy) (E : ℝ)
    (hE : spectralGround energy ≤ E)
    (rho sigma : (n : ℕ) → State ((Fin (n + 1) → I) × (Fin (n + 1) → J)))
    (hrho : ∀ n, coefficientEnergy (additiveEnergy energy (n + 1))
      (traceSecond (rho n).coefficients) ≤ ENNReal.ofReal ((n + 1 : ℝ) * E))
    (hsigma : ∀ n, coefficientEnergy (additiveEnergy energy (n + 1))
      (traceSecond (sigma n).coefficients) ≤ ENNReal.ofReal ((n + 1 : ℝ) * E))
    (hdist : Tendsto (fun n => nuclearStateDistance (rho n) (sigma n)) atTop (nhds 0)) :
    (∀ n, countableRelativeEntanglementNats (rho n).coefficients < ⊤ ∧
      countableRelativeEntanglementNats (sigma n).coefficients < ⊤ ∧
      regularizedCountableEntanglementNats (rho n).coefficients < ⊤ ∧
      regularizedCountableEntanglementNats (sigma n).coefficients < ⊤) ∧
    Tendsto (fun n =>
      |(countableRelativeEntanglementNats (rho n).coefficients).toReal -
        (countableRelativeEntanglementNats (sigma n).coefficients).toReal| / (n + 1 : ℝ))
      atTop (nhds 0) ∧
    Tendsto (fun n =>
      |(regularizedCountableEntanglementNats (rho n).coefficients).toReal -
        (regularizedCountableEntanglementNats (sigma n).coefficients).toReal| / (n + 1 : ℝ))
      atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Support50.P18

end
