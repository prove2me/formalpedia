-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_parallel_success_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.parallel_success_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:28:08.704899+00:00
-- url     : https://prove2.me/theorems/0ce23b9c-62dd-4aa9-a0c2-577a45f7fe65
-- title:
--   Universal parallel inversion success bound
-- statement:
--   Let $d\ge2$ and $k\ge0$ be integers. Suppose a fixed universal parallel heralded protocol uses $k$ forward calls to the same unknown $U\in SU(d)$ and has success branch $\rho\mapsto p_P U^\dagger\rho U$ for every $U$, including reference-entangled inputs, with $p_P\in[0,1]$ independent of $U$ and the input. Then
--
--   $$p_P\le1-\frac{d+1}{k+d^2-1}.$$
--
--   Parallel means that the calls constitute one collective $U^{\otimes k}$ slot, with arbitrary memory and fixed preprocessing and postprocessing, and no gates between the calls. No inverse, controlled oracle, or description of $U$ is supplied. Equality of inverse channels makes scalar phases immaterial.
--
--   The inequality applies to every such protocol and gives an inverse-linear lower bound on its failure probability for fixed $d$.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 3, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.3, Theorem 2: every universal exact parallel protocol obeys this bound. -/
theorem parallel_success_bound (d k : ℕ) (hd : 2 ≤ d) (p : ℝ)
    (hp : Attainable .parallel d k p) :
    p ≤ 1 - ((d : ℝ)+1) / ((k : ℝ)+(d : ℝ)^2-1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
