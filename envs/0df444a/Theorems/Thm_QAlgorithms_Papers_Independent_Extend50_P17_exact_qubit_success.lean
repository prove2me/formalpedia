-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_exact_qubit_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.exact_qubit_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:55:45.472982+00:00
-- url     : https://prove2.me/theorems/351ea5bb-2b8d-488a-a3cc-32258f8bc296
-- title:
--   Eq.(14) and Appendix C / Eqs.(71)–(73): exact qubit success probability
-- statement:
--   For integers $1\le k\le N$, let $p_{\rm succ}(N,k)$ be the maximum success probability of conclusive qubit MPBT using $N$ fixed normalized maximally entangled pairs. Each successful branch transfers the entire input perfectly, including correlations with a reference, by selecting and reordering distinct output ports. An additional outcome signals failure. Then the optimum is attained and
--
--   $$p_{\rm succ}(N,k)=\frac1{2^N(N+1)}\sum_{r=0}^{\lfloor(N-k)/2\rfloor}(N-k-2r+1)^2\binom{N+1}{r}.$$
--
--   The substitution $s=(N-k)/2-r$ gives Eq. (14). This optimizes the conclusive measurement only, and differs from deterministic SRM discrimination. Eq. (73) incorrectly omits the squared weight.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 6, Eq.(14) and Appendix C / Eqs.(71)–(73): exact qubit success probability

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Eq.(14), and p.14, Eq.(71): optimal conclusive success at fixed EPR resource.
Eq.(73) drops the indispensable (2s+1)^2 weight and is not used. -/
theorem exact_qubit_success (N k : ℕ) (hk : 1 ≤ k) (hNk : k ≤ N) :
    mpbtSuccessProbability 2 N k = qubitSuccessExpression N k ∧
    ∃ (E : MPBTPortSelection N k → AliceOp 2 N k) (p : MPBTPortSelection N k → ℝ),
      Conclusive (eprResource 2 N) E p ∧
      (∑ a, p a) = qubitSuccessExpression N k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
