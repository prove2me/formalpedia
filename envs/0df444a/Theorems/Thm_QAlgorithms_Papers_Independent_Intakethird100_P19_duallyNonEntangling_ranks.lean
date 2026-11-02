-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_duallyNonEntangling_ranks
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.duallyNonEntangling_ranks
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:36:25.319438+00:00
-- url     : https://prove2.me/theorems/900b70d5-27b0-4ed2-9986-59dabc81c40f
-- title:
--   Theorem 9: arbitrary Schmidt ranks under dually non-entangling channels
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. For every pair of integers $k,d\ge2$, there exist pure states $\psi$ on $k\times k$ and $\varphi$ on $d\times d$, and a dually non-entangling channel $\Lambda$, such that
--
--   $$\operatorname{SR}(\psi)=k,\quad\operatorname{SR}(\varphi)=d,\quad\Lambda(\psi)=\varphi.$$
--
--   The two ranks need not be ordered.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 12, Theorem 9

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

/-- Theorem 9, PDF pp.12-13: arbitrary two positive Schmidt ranks at least two
can be connected by a dually non-entangling channel, with no k<d restriction. -/
theorem duallyNonEntangling_ranks (k d : ℕ) (hk : 2 ≤ k) (hd : 2 ≤ d) :
    ∃ psi : UnitBipartiteKet k k, ∃ phi : UnitBipartiteKet d d,
      ∃ L : Superop (Fin k × Fin k) (Fin d × Fin d),
        finiteSchmidtRank psi.ket = k ∧ finiteSchmidtRank phi.ket = d ∧
        IsChannel L ∧ DNE L ∧ L psi.rho = phi.rho := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
