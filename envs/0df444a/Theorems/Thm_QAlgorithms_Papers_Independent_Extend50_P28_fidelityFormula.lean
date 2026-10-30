-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_fidelityFormula
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.fidelityFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:20:51.202458+00:00
-- url     : https://prove2.me/theorems/03b65339-5c63-4051-be58-d26ad00972cc
-- title:
--   Deterministic PBT fidelity from representation dimensions and multiplicities
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Put $\sigma_a=d^{-N}T_a$ and $\widetilde\rho=\sum_a\sigma_a$. The standard deterministic PBT entanglement fidelity for $N$ normalized maximally entangled resource pairs and the completed square-root measurement is the computed quantity $F_n(d)=d^{-2}\sum_a\operatorname{Tr}(\sigma_a\widetilde\rho^{-1/2}\sigma_a\widetilde\rho^{-1/2})$. Every inverse half-power is the spectral support inverse, equal to zero on the kernel. A branch $\mu\supset\alpha$ adds one box; both shapes have at most d rows. Then
--
--   $$
--   F_n(d)=\frac{1}{d^{n+1}}\sum_{\substack{\alpha\vdash n-2\\h(\alpha)\le d}}\left(\sum_{\substack{\mu\vdash n-1,\,\mu\supset\alpha\\h(\mu)\le d}}\sqrt{d_\mu m_\mu}\right)^2.
--   $$
--
--   The outer sum remains outside the square, and the denominator is d^(N+2). The source rederives this result and credits independent work [28].
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 24, Section 5.3 unnumbered main result

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.24, Eq.(120): deterministic PBT entanglement fidelity. The sum
over physical lower shapes is outside the square; both multiplicities are actual
Specht occurrence counts. N=n-1, so d^(N+2)=d^(n+1). -/
theorem fidelityFormula (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    pbtFidelity d (n - 1) =
      (∑ alpha : QAlgorithms.Schur.Partition d (n - 2),
        (∑ nu : QAlgorithms.Schur.Partition d (n - 1),
          if alpha.val.cells ⊆ nu.val.cells then
            Real.sqrt ((irrepDim nu : ℝ) * (tensorMultiplicity d nu : ℝ)) else 0) ^ 2) /
      (d : ℝ) ^ (n + 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
