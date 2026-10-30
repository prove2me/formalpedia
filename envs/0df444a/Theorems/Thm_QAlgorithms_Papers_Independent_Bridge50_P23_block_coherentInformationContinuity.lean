-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_block_coherentInformationContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.block_coherentInformationContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:32:11.771991+00:00
-- url     : https://prove2.me/theorems/70987954-8bb0-4daa-8199-e6e36971b0c9
-- title:
--   §V unnumbered: block coherent-information continuity bound
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\mathcal N_1,\mathcal N_2:A\to B$ be CPTP channels, let $H_A,H_B$ be grounded, and assume $\operatorname{Tr}e^{-\beta H_B}<\infty$ for every $\beta>0$. Fix common constants $\alpha,E_0\ge0$ such that $\operatorname{Tr}\mathcal N_i(\rho)H_B\le\alpha\operatorname{Tr}\rho H_A+E_0$ for every finite-energy input state and $i=1,2$. For $E>0$ and $0\le\varepsilon<1$, assume $\tfrac12\|\mathcal N_1-\mathcal N_2\|_{\diamond E}\le\varepsilon$. Write $F_B(L)=S(\gamma_B(L))$ for the maximal von Neumann entropy, in nats, at energy at most $L$, and $g(x)=(1+x)\log(1+x)-x\log x$. For $0<\varepsilon<1$, put $\delta=\sqrt{\varepsilon}$, $\widetilde E=\alpha E+E_0$, and $$M_B(\widetilde E,\varepsilon)=56\delta F_B(4\widetilde E/\delta)+6g(4\delta).$$ At $\varepsilon=0$ use its continuous extension, $M_B=0$. For every $n\ge1$, let $Q^{(1)}(\mathcal N_i^{\otimes n},nE)$ be the supremum of coherent information over inputs with total mean energy at most $nE$. Coherent information is $I(R:B^n)-S(R)$ on a purification, with the channel acting on the constrained input half. Then $$\frac1n|Q^{(1)}(\mathcal N_1^{\otimes n},nE)-Q^{(1)}(\mathcal N_2^{\otimes n},nE)|\le M_B(\widetilde E,\varepsilon).$$ Output Gibbs and the affine energy bound give finite output entropy. If the input entropy is infinite, coherent information is minus infinity; its clipped contribution is zero. Pure feasible inputs give zero, so clipping does not change the supremum. This supplies the quantum-capacity regularization bound.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 11, §V unnumbered: block coherent-information continuity bound

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

/-- Section V, PDF p.11: block optimized coherent-information continuity.
Printed Delta in Q^(1)'s definition is replaced by the channel N, as the surrounding
text requires. The channel acts on the constrained input, not its reference.
Only output Gibbs is assumed as in Lemma 8. Infinite-input-entropy states
have coherent information minus infinity and contribute zero to the clipped supremum. -/
theorem block_coherentInformationContinuity {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (G : PositiveObservable J)
    (hH : Grounded H) (hG : Grounded G) (hgibbsG : GibbsCondition G)
    (N M : Channel I J) (alpha offset : ℝ) (ha : 0 ≤ alpha) (ho : 0 ≤ offset)
    (hN : AffineEnergyLimited H G alpha offset N.val) (hM : AffineEnergyLimited H G alpha offset M.val) :
    ∀ (n : ℕ), 0 < n → ∀ E eps : ℝ, 0 < E → 0 ≤ eps → eps < 1 →
    energyMagnitude H E (fun X => N.val X - M.val X) ≤ ENNReal.ofReal (2 * eps) →
    |(energyConstrainedBlockCoherentInformation N.val H n ((n : ℝ) * E)).toReal -
      (energyConstrainedBlockCoherentInformation M.val H n ((n : ℝ) * E)).toReal| / (n : ℝ) ≤
      capacityBound G (alpha * E + offset) eps := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
