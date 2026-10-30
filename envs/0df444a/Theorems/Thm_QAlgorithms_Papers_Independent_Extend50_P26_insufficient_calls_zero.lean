-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P26_insufficient_calls_zero
-- name    : QAlgorithms.Papers.Independent.Extend50.P26.insufficient_calls_zero
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:29:28.62896+00:00
-- url     : https://prove2.me/theorems/d9727333-4560-4e57-ba32-9e82146f75de
-- title:
--   Zero exact success below d−1 calls, including indefinite causal order
-- statement:
--   Let $d\ge2$ and $0\le k<d-1$ be integers. Consider any fixed heralded inversion process using $k$ forward calls to the same unknown $U\in SU(d)$, allowing indefinite causal order in the paper's process-matrix model. Suppose its success branch is $\rho\mapsto p_S U^\dagger\rho U$ for every $U$, with $p_S\in[0,1]$ independent of $U$ and of the input, including reference-entangled inputs. Then
--
--   $$p_S=0.$$
--
--   Admissibility requires a positive deterministic completion normalized on arbitrary independent CPTP channels in its slots, and a positive success operator dominated by that completion. Only the forward physical operation is available. A positive success probability is not assumed.
--
--   The obstruction includes $k=0$ and applies to the full process class, hence in particular to parallel and adaptive circuits.
-- source:
--   Reversing Unknown Quantum Transformations: Universal Quantum Circuit for Inverting General Unitary Operations, arXiv:1810.06944v3, PDF p. 3, Theorem 3; proof continues on p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P26

noncomputable section

open QAlgorithms

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Extend50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF pp.3–4, Theorem 3: the zero-success obstruction includes general processes
without definite causal order, and includes zero calls. -/
theorem insufficient_calls_zero (d k : ℕ) (hd : 2 ≤ d) (hk : k < d-1)
    (p : ℝ) (hp : Attainable .indefinite d k p) : p = 0 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P26

end
