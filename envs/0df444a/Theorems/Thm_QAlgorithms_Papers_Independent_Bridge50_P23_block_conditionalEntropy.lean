-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_block_conditionalEntropy
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.block_conditionalEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:30:41.423096+00:00
-- url     : https://prove2.me/theorems/fe94725d-08ab-4bfa-80ec-55c19834f6ea
-- title:
--   Lemma 8: n-letter conditional entropy continuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\mathcal N_1,\mathcal N_2:A\to B$ be channels, with $H_B$ satisfying the Gibbs hypothesis. Fix $\alpha,E_0\ge0$ such that both channels obey $\operatorname{Tr}\mathcal N_i(\rho)H_B\le\alpha\operatorname{Tr}\rho H_A+E_0$ at every finite-energy input. For $E>0$ and $0\le\varepsilon<1$, suppose $\tfrac12\|\mathcal N_1-\mathcal N_2\|_{\diamond E}\le\varepsilon$. Let $n\ge1$ and let $\rho^{A^n C}$ have total input energy at most $nE$. Define $\omega_n=(\mathcal N_1^{\otimes n}\otimes\mathrm{id}_C)(\rho)$ and $\omega_0=(\mathcal N_2^{\otimes n}\otimes\mathrm{id}_C)(\rho)$. With $\delta=\sqrt\varepsilon$, $\widetilde E=\alpha E+E_0$ and $F_B(L)=S(\gamma_B(L))$, $$\frac1n|S(B^n|C)_{\omega_n}-S(B^n|C)_{\omega_0}|\le14\delta(1+\delta)F_B((1+3\delta)\widetilde E/\delta)+3g(2\delta(1+\delta))\le28\delta F_B(4\widetilde E/\delta)+3g(4\delta).$$ Use the continuous zero value at $\varepsilon=0$. Conditional entropy uses its finite-first-entropy extension, allowing infinite reference entropy. This is a block-length-uniform mean-energy bound.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 10, Lemma 8: n-letter conditional entropy continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P23

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P23

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsTraceClass traceSize tensorApply rankOne productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel traceSecond traceFirst homogeneousEntropy generalizedRelativeEntropy
   channelTensorAction finiteInputCoherentInfo)

open QAlgorithms.Papers.Independent.Frontier18.P08 (IsQuantumOperation)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable closedFormExpectation GibbsCondition TensorBlockIndex blockAction blockEnergy)

open QAlgorithms.Papers.Independent.Claimed50.P18 (finiteFirstConditionalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 8, PDF pp.9--11, equation (7). Printed total=average is changed to
SUM<=nE, as the preceding definition and p.10 proof require. Individual site
energies may exceed E. Zero-error formulas use their continuous extension.
Independent correction moderation remains pending. -/
theorem block_conditionalEntropy {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (G : PositiveObservable J)
    (hH : Grounded H) (hG : Grounded G) (hgibbs : GibbsCondition G)
    (N M : Channel I J) (alpha offset : ℝ) (ha : 0 ≤ alpha) (ho : 0 ≤ offset)
    (hN : AffineEnergyLimited H G alpha offset N.val) (hM : AffineEnergyLimited H G alpha offset M.val) :
    ∀ (C : Type) [Countable C] [Nonempty C] (n : ℕ), 0 < n →
    ∀ E eps : ℝ, 0 < E → 0 ≤ eps → eps < 1 →
    energyMagnitude H E (fun X => N.val X - M.val X) ≤ ENNReal.ofReal (2 * eps) →
    ∀ rho : State (TensorBlockIndex I n × C),
    blockEnergy H n (traceSecond rho.coefficients) ≤ ENNReal.ofReal ((n : ℝ) * E) →
    |conditionalEntropyValue (tensorApply (blockAction N.val n) rho.coefficients) -
     conditionalEntropyValue (tensorApply (blockAction M.val n) rho.coefficients)| / (n : ℝ) ≤
      blockEntropyBound G (alpha * E + offset) eps ∧
    blockEntropyBound G (alpha * E + offset) eps ≤ simpleEntropyBound G (alpha * E + offset) eps := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
