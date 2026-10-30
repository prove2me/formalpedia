-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_energyNorm_axioms
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.energyNorm_axioms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:24:27.867549+00:00
-- url     : https://prove2.me/theorems/b7c459e3-cb9f-4dda-a8c7-0c80bfb5dcc0
-- title:
--   Lemma 4(1)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. For every $E>0$, the function $\Delta\mapsto\|\Delta\|_{\diamond E}$ is a finite norm on the real vector space of the source superoperators. Explicitly, $$\|\Delta\|_{\diamond E}=0\iff\Delta=0,\qquad\|\Delta+\Theta\|_{\diamond E}\le\|\Delta\|_{\diamond E}+\|\Theta\|_{\diamond E},\qquad\|r\Delta\|_{\diamond E}=|r|\|\Delta\|_{\diamond E}\quad(r\in\mathbb R).$$ Equality of maps is equality on trace-class inputs. This makes the constrained distinguishability functional a genuine norm.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 5, Lemma 4(1)

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

/-- Lemma 4(1), PDF p.5: all norm axioms over the real HP superoperator
space, with equality of maps tested only on trace class. Finiteness is explicit. -/
theorem energyNorm_axioms {I J : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] (H : PositiveObservable I) (hH : Grounded H)
    (E : ℝ) (hE : 0 < E) :
    (∀ D : Matrix I I ℂ → Matrix J J ℂ, IsSuperoperator D →
      energyMagnitude H E D < ⊤ ∧
      (energyMagnitude H E D = 0 ↔ ∀ X, IsTraceClass X → D X = 0)) ∧
    (∀ D T : Matrix I I ℂ → Matrix J J ℂ, IsSuperoperator D → IsSuperoperator T →
      energyMagnitude H E (fun X => D X + T X) ≤
        energyMagnitude H E D + energyMagnitude H E T) ∧
    (∀ (r : ℝ) (D : Matrix I I ℂ → Matrix J J ℂ), IsSuperoperator D →
      energyMagnitude H E (fun X => (r : ℂ) • D X) =
        ENNReal.ofReal |r| * energyMagnitude H E D) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
