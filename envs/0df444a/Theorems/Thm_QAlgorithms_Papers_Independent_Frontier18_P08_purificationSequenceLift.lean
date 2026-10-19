-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P08_purificationSequenceLift
-- name    : QAlgorithms.Papers.Independent.Frontier18.P08.purificationSequenceLift
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:54:59.828434+00:00
-- url     : https://prove2.me/theorems/383a2b4c-5f3e-47d1-810b-bf3b063c2065
-- title:
--   Lemma 1: lifting convergent marginals to pure states
-- statement:
--   Let $H$ and $K$ be separable complex Hilbert spaces of equal Hilbert dimension, and let $\omega_0$ be a specified pure normalized state on the completed tensor product $H\otimes K$. Suppose $(\rho_k)$ is a sequence of normalized trace-class states on $H$ converging in trace norm to $\operatorname{Tr}_K\omega_0$. There exists a sequence of pure normalized states $(\omega_k)$ on $H\otimes K$ such that
--
--   $$
--   \|\omega_k-\omega_0\|_1\longrightarrow0,
--   \qquad \operatorname{Tr}_K\omega_k=\rho_k\quad\text{for every }k.
--   $$
--
--   This permits continuity arguments to retain a prescribed limiting purification. Countable orthonormal coordinates model the Hilbert spaces, and equality of basis cardinalities expresses equality of Hilbert dimension.
-- source:
--   Measures of quantum correlations in infinite-dimensional systems, arXiv:1506.06377v2, PDF p. 7, Lemma 1: lifting convergent marginals to pure states

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

noncomputable section

open Filter

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P08

open QAlgorithms

open QAlgorithms.RealRegisters (Hilbert)

/-- Lemma 1, PDF p.7: lift a trace-norm convergent marginal sequence to pure
states converging to the specified purification. Equal Hilbert dimensions
are equality of orthonormal-basis cardinalities, including infinite dimension. -/
theorem purificationSequenceLift {I J : Type} [Countable I] [Countable J]
    (hDim : Nonempty (I ≃ J)) (omega0 : Accepted.PureState (I × J))
    (rho : ℕ → Accepted.State I)
    (hConverges : TraceNormConverges (fun k => (rho k).coefficients)
      (partialTraceSecond omega0.val.coefficients)) :
    ∃ omega : ℕ → Accepted.PureState (I × J),
      TraceNormConverges (fun k => (omega k).val.coefficients) omega0.val.coefficients ∧
      ∀ k, (rho k).coefficients = partialTraceSecond (omega k).val.coefficients := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P08

end
