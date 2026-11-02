-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_schmidtRank_increase
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.schmidtRank_increase
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:31:35.196595+00:00
-- url     : https://prove2.me/theorems/ec3751c7-bdf2-44b5-b164-8a22b8373d10
-- title:
--   Corollary 2: non-entangling channels can increase Schmidt rank
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. A non-entangling map is completely positive and preserves the full separable positive cone. A channel is also trace preserving. For integers $2\le k<d$, there exist a pure state $\varphi$ on $\mathbb C^d\otimes\mathbb C^d$ and a non-entangling channel $\Lambda$ from $k\times k$ to $d\times d$ such that
--
--   $$\Lambda(\phi_k^+)=\varphi,\qquad \operatorname{SR}(\varphi)=d.$$
--
--   Schmidt rank counts the positive squared Schmidt coefficients. This witnesses failure of Schmidt-rank monotonicity.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 9, Corollary 2

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

/-- Corollary 2, PDF p.9: currency of rank k can produce a pure state of rank d>k. -/
theorem schmidtRank_increase (k d : ℕ) (hk : 2 ≤ k) (hkd : k < d) :
    ∃ phi : UnitBipartiteKet d d, ∃ L : Superop (Fin k × Fin k) (Fin d × Fin d),
      IsChannel L ∧ NE L ∧ L (epr k) = phi.rho ∧ finiteSchmidtRank phi.ket = d := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
