-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_capacities_uniformContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.capacities_uniformContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:32:57.164038+00:00
-- url     : https://prove2.me/theorems/9b3ecc1e-6fcd-4855-bf2a-f9dc0aaae087
-- title:
--   Theorem 9: uniform continuity bounds for energy-constrained classical and quantum capacities
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\mathcal N_1,\mathcal N_2:A\to B$ be CPTP channels, and let the grounded Hamiltonians $H_A,H_B$ satisfy $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Fix common constants $\alpha,E_0\ge0$ such that $\operatorname{Tr}\mathcal N_i(\rho)H_B\le\alpha\operatorname{Tr}\rho H_A+E_0$ for every finite-energy input state and $i=1,2$. For $E>0$ and $0\le\varepsilon<1$, assume $\tfrac12\|\mathcal N_1-\mathcal N_2\|_{\diamond E}\le\varepsilon$. Write $F_B(L)=S(\gamma_B(L))$ for the maximal von Neumann entropy, in nats, at energy at most $L$, and $g(x)=(1+x)\log(1+x)-x\log x$. For $0<\varepsilon<1$, put $\delta=\sqrt{\varepsilon}$, $\widetilde E=\alpha E+E_0$, and $$M_B(\widetilde E,\varepsilon)=56\delta F_B(4\widetilde E/\delta)+6g(4\delta).$$ At $\varepsilon=0$ use its continuous extension, $M_B=0$. Let $C(\mathcal N,E)=\sup_{n\ge1}n^{-1}\chi(\mathcal N^{\otimes n},nE)$ and $Q(\mathcal N,E)=\sup_{n\ge1}n^{-1}Q^{(1)}(\mathcal N^{\otimes n},nE)$ be the energy-constrained classical and quantum capacities in nats. Then $$|C(\mathcal N_1,E)-C(\mathcal N_2,E)|\le M_B(\widetilde E,\varepsilon),\qquad |Q(\mathcal N_1,E)-Q(\mathcal N_2,E)|\le M_B(\widetilde E,\varepsilon).$$ The common energy constants precede the budget and error, and the bound applies to both capacities. It gives uniform continuity under a mean input-energy constraint.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 12, Theorem 9: uniform continuity bounds for energy-constrained classical and quantum capacities

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

/-- Theorem 9, PDF p.12, with capacity regularizations on p.11: BOTH
classical and quantum bounds, in nats, with constants 56 and 6. Common affine
constants precede budget and error; Gibbs is required on both systems. Printed
quotients at zero error use the explicit continuous zero branch: zero ECD distance
at positive budget identifies the channels and gives zero capacity difference. -/
theorem capacities_uniformContinuity {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (G : PositiveObservable J)
    (hH : Grounded H) (hG : Grounded G) (hgibbsH : GibbsCondition H) (hgibbsG : GibbsCondition G)
    (N M : Channel I J) (alpha offset : ℝ) (ha : 0 ≤ alpha) (ho : 0 ≤ offset)
    (hN : AffineEnergyLimited H G alpha offset N.val) (hM : AffineEnergyLimited H G alpha offset M.val) :
    ∀ E eps : ℝ, 0 < E → 0 ≤ eps → eps < 1 →
    energyMagnitude H E (fun X => N.val X - M.val X) ≤ ENNReal.ofReal (2 * eps) →
    |(energyConstrainedClassicalCapacity N.val H E).toReal - (energyConstrainedClassicalCapacity M.val H E).toReal| ≤
      capacityBound G (alpha * E + offset) eps ∧
    |(energyConstrainedQuantumCapacity N.val H E).toReal - (energyConstrainedQuantumCapacity M.val H E).toReal| ≤
      capacityBound G (alpha * E + offset) eps := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
