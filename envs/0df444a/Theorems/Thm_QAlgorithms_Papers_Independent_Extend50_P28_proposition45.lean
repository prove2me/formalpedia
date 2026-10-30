-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_proposition45
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.proposition45
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:16:08.546995+00:00
-- url     : https://prove2.me/theorems/a298f0cf-51b3-488b-b822-d957f03a0578
-- title:
--   Unnormalized PBT operator trace
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces.
--
--   $$
--   \operatorname{Tr}_H\rho=(n-1)d^{n-1}.
--   $$
--
--   The trace is taken on the full tensor space without state normalization.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 21, Proposition 45

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.21, Proposition 45, Eq.(103): full, unnormalized tensor trace. -/
theorem proposition45 (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (pbtOperator d (n - 1)).trace = (((n : ℂ) - 1) * (d : ℂ) ^ (n - 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
