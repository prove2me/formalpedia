-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_block_holevoContinuity
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.block_holevoContinuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:31:29.437909+00:00
-- url     : https://prove2.me/theorems/6ea65f37-2847-4fb1-adf5-cf48f125f6af
-- title:
--   §V unnumbered: block Holevo continuity bound
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\mathcal N_1,\mathcal N_2:A\to B$ be CPTP channels, let $H_A,H_B$ be grounded, and assume $\operatorname{Tr}e^{-\beta H_B}<\infty$ for every $\beta>0$. Fix common constants $\alpha,E_0\ge0$ such that $\operatorname{Tr}\mathcal N_i(\rho)H_B\le\alpha\operatorname{Tr}\rho H_A+E_0$ for every finite-energy input state and $i=1,2$. For $E>0$ and $0\le\varepsilon<1$, assume $\tfrac12\|\mathcal N_1-\mathcal N_2\|_{\diamond E}\le\varepsilon$. Write $F_B(L)=S(\gamma_B(L))$ for the maximal von Neumann entropy, in nats, at energy at most $L$, and $g(x)=(1+x)\log(1+x)-x\log x$. For $0<\varepsilon<1$, put $\delta=\sqrt{\varepsilon}$, $\widetilde E=\alpha E+E_0$, and $$M_B(\widetilde E,\varepsilon)=56\delta F_B(4\widetilde E/\delta)+6g(4\delta).$$ At $\varepsilon=0$ use its continuous extension, $M_B=0$. For every $n\ge1$, let $\chi(\mathcal N_i^{\otimes n},nE)$ be the supremum of the output Holevo quantity over ensembles with average total input energy at most $nE$. Then $$\frac1n|\chi(\mathcal N_1^{\otimes n},nE)-\chi(\mathcal N_2^{\otimes n},nE)|\le M_B(\widetilde E,\varepsilon).$$ Finite mixed ensembles give the same supremum as pure ensembles by refinement, with countable ensembles obtained by approximation preserving the average constraint. This bound is independent of block length.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 11, §V unnumbered: block Holevo continuity bound

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

/-- Section V, PDF p.11: block Holevo continuity at total INPUT energy nE.
The output label in the source's energy constraint is corrected to the input,
matching its explicit average-input formula. Only the output Gibbs condition
from Lemma 8 is required; input Gibbs first appears in Theorem 9. -/
theorem block_holevoContinuity {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (G : PositiveObservable J)
    (hH : Grounded H) (hG : Grounded G) (hgibbsG : GibbsCondition G)
    (N M : Channel I J) (alpha offset : ℝ) (ha : 0 ≤ alpha) (ho : 0 ≤ offset)
    (hN : AffineEnergyLimited H G alpha offset N.val) (hM : AffineEnergyLimited H G alpha offset M.val) :
    ∀ (n : ℕ), 0 < n → ∀ E eps : ℝ, 0 < E → 0 ≤ eps → eps < 1 →
    energyMagnitude H E (fun X => N.val X - M.val X) ≤ ENNReal.ofReal (2 * eps) →
    |(blockHolevo N.val H n ((n : ℝ) * E)).toReal - (blockHolevo M.val H n ((n : ℝ) * E)).toReal| / (n : ℝ) ≤
      capacityBound G (alpha * E + offset) eps := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
