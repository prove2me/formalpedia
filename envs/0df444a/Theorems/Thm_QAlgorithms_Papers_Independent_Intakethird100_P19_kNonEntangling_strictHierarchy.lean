-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_kNonEntangling_strictHierarchy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.kNonEntangling_strictHierarchy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:43:31.152677+00:00
-- url     : https://prove2.me/theorems/a04d403e-02c2-458b-afb0-00bd924ac21a
-- title:
--   Theorem 20: strict hierarchy of k-non-entangling maps
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. For every $2\le k<d$, there exists a completely positive map $\Lambda$ from $\mathbb C^d\otimes\mathbb C^d$ to two qubits such that
--
--   $$\Lambda\text{ is }k\text{-non-entangling},\qquad \Lambda\text{ is not }(k+1)\text{-non-entangling}.$$
--
--   Each nontrivial adjacent level of the hierarchy is distinct.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 22, Theorem 20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Theorem 20, PDF pp.22-23: strictness of each k-non-entangling level,
for CP maps from d-by-d to two qubits; TP is not a hypothesis. -/
theorem kNonEntangling_strictHierarchy (k d : ℕ) (hk : 2 ≤ k) (hkd : k < d) :
    ∃ L : Superop (Fin d × Fin d) (Fin 2 × Fin 2),
      CP L ∧ KNE k L ∧ ¬ KNE (k + 1) L := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
