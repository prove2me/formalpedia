-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_proposition48
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.proposition48
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:16:49.769988+00:00
-- url     : https://prove2.me/theorems/bbbd10cf-5a2b-4092-88b2-57dcebbfc4ed
-- title:
--   Largest PBT eigenvalue and its multiplicity
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. For a permutation $\sigma$, let $\ell(\sigma)$ count all cycles, including fixed points. Then
--
--   $$
--   \lambda_{\max}(\rho)=d+n-2,\qquad \dim\ker(\rho-(d+n-2)I)=\frac{1}{(n-2)!}\sum_{\sigma\in S(n-2)}d^{\ell(\sigma)}.
--   $$
--
--   Existence of a nonzero eigenvector, the bound on every real eigenvalue, and full spectral multiplicity are all included. The empty permutation group at n=2 has one element and zero cycles.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 22, Proposition 48

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.22, Proposition 48: actual largest eigenvalue, no larger real
eigenvalue, and its full eigenspace multiplicity, including n=2. -/
theorem proposition48 (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    (∃ v : Word d ((n - 1) + 1) → ℂ, v ≠ 0 ∧
      (pbtOperator d (n - 1)).mulVec v = (((d : ℝ) + n - 2 : ℝ) : ℂ) • v) ∧
    (∀ (lambda : ℝ) (v : Word d ((n - 1) + 1) → ℂ), v ≠ 0 →
      (pbtOperator d (n - 1)).mulVec v = (lambda : ℂ) • v → lambda ≤ (d : ℝ) + n - 2) ∧
    (eigenMultiplicity (pbtOperator d (n - 1)) ((d : ℝ) + n - 2) : ℝ) =
      (∑ sigma : Equiv.Perm (Fin (n - 2)), (d : ℝ) ^ cycleCount sigma) /
        ((n - 2).factorial : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
