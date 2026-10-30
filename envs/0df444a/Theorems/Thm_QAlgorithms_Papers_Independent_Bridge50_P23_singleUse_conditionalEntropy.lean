-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P23_singleUse_conditionalEntropy
-- name    : QAlgorithms.Papers.Independent.Bridge50.P23.singleUse_conditionalEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:29:09.82993+00:00
-- url     : https://prove2.me/theorems/c62fcc0e-eb2b-43af-b243-2049d8f12448
-- title:
--   Lemma 7: single-use conditional entropy bounds
-- statement:
--   All systems are nonzero separable complex Hilbert spaces. States are positive trace-class operators of trace one. Trace norms have no factor one half, except where displayed. A grounded Hamiltonian is a densely defined nonnegative self-adjoint operator with infimum energy zero and dense finite-energy form domain; continuous spectrum is allowed. The energy-constrained diamond norm constrains only the input marginal, with unrestricted reference and measurement. Let $\mathcal N_1,\mathcal N_2:A\to B$ be channels and assume $\tfrac12\|\mathcal N_1-\mathcal N_2\|_{\diamond E}\le\varepsilon<1$, with $E>0$ and $\varepsilon\ge0$. Let $H_B$ be grounded and satisfy the Gibbs hypothesis at every positive inverse temperature. For any state $\rho^{AC}$ with input energy at most $E$, put $\omega_i=(\mathcal N_i\otimes\mathrm{id})(\rho)$ and suppose both output marginal energies are at most $F\ge0$. Write $F_B(L)=S(\gamma_B(L))$ and $g(x)=(1+x)\log(1+x)-x\log x$. For every $\varepsilon<\varepsilon'\le1$, let $d=(\varepsilon'-\varepsilon)/(1+\varepsilon')$. Then $$|S(B|C)_{\omega_1}-S(B|C)_{\omega_2}|\le6\varepsilon' F_B(F/d)+3g(\varepsilon'),\qquad |S(B|C)_{\omega_1}-S(B|C)_{\omega_2}|\le2F_B(F).$$ Conditional entropy means its finite-first-entropy extension $S(B)-I(B:C)$; no finite entropy of $C$ is required. These bounds control a single use without a global output-energy bound on all inputs.
-- source:
--   Energy-constrained diamond norm with applications to the uniform continuity of continuous variable channel capacities, arXiv:1712.10267v1, PDF p. 9, Lemma 7: single-use conditional entropy bounds

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

/-- Lemma 7, PDF pp.8--9, equations (5),(6): both absolute values checked
on the PDF. Output budget F is independent of input budget E. -/
theorem singleUse_conditionalEntropy {I J C : Type} [Countable I] [Nonempty I]
    [Countable J] [Nonempty J] [Countable C] [Nonempty C]
    (H : PositiveObservable I) (G : PositiveObservable J) (hH : Grounded H)
    (hG : Grounded G) (hgibbs : GibbsCondition G) (N M : Channel I J)
    (E F eps : ℝ) (hE : 0 < E) (hF : 0 ≤ F) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hclose : energyMagnitude H E (fun X => N.val X - M.val X) ≤ ENNReal.ofReal (2 * eps))
    (rho : State (I × C))
    (hin : closedFormExpectation H (traceSecond rho.coefficients) ≤ ENNReal.ofReal E)
    (houtN : closedFormExpectation G (traceSecond (tensorApply N.val rho.coefficients)) ≤ ENNReal.ofReal F)
    (houtM : closedFormExpectation G (traceSecond (tensorApply M.val rho.coefficients)) ≤ ENNReal.ofReal F) :
    (∀ ep : ℝ, eps < ep → ep ≤ 1 →
      |conditionalEntropyValue (tensorApply N.val rho.coefficients) -
       conditionalEntropyValue (tensorApply M.val rho.coefficients)| ≤
        6 * ep * (maximumEntropy G (F / ((ep - eps) / (1 + ep)))).toReal + 3 * g ep) ∧
    |conditionalEntropyValue (tensorApply N.val rho.coefficients) -
     conditionalEntropyValue (tensorApply M.val rho.coefficients)| ≤
      2 * (maximumEntropy G F).toReal := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P23

end
