-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_naturalTraceFormula
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.naturalTraceFormula
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:20:05.564995+00:00
-- url     : https://prove2.me/theorems/5fbe90db-ca7d-47c8-b454-0d43cf5eb156
-- title:
--   Natural-representation PBT trace and multiplicity average
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. For physical $\alpha$, sum over every retained branch $\nu,\mu\supset\alpha$, and let $\lambda_\nu(\alpha)=d+c(\nu/\alpha)$. For any port $a$,
--
--   $$
--   \operatorname{Tr}_H(\rho^{-1/2}T_a\rho^{-1/2}T_a)=\frac{1}{(n-1)^2}\sum_{h(\alpha)\le d}\frac{m_\alpha}{d_\alpha}\sum_{\nu,\mu\supset\alpha}d_\nu d_\mu\sqrt{\lambda_\nu(\alpha)\lambda_\mu(\alpha)},\qquad m_\alpha=\frac{1}{(n-2)!}\sum_{\sigma\in S(n-2)}\chi^\alpha(\sigma^{-1})d^{\ell(\sigma)}.
--   $$
--
--   The trace equality is complex equality to the displayed real scalar, also fixing its imaginary part. This retains (118)–(119) without asserting the false regular specialization (117).
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 24, Corollary 51(b), independently valid natural trace

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.24, Corollary 51(b), Eqs.(118)–(119), with n=k+2: the independently
valid natural specialization. All retained branches, actual multiplicities, and
the single d_alpha in the denominator are explicit. The complex equality also
asserts that the trace has zero imaginary part. -/
theorem naturalTraceFormula (k d : ℕ) (hd : 2 ≤ d) (a : Fin (k + 1)) :
    naturalTrace d (k + 1) a =
      (((∑ alpha : PhysicalLower d k,
        (tensorMultiplicity d alpha.val : ℝ) / (irrepDim alpha.val : ℝ) *
          ∑ nu : Retained d alpha.val, ∑ mu : Retained d alpha.val,
            (irrepDim nu.val.val : ℝ) * (irrepDim mu.val.val : ℝ) *
              Real.sqrt (contentEigenvalue d alpha.val.val nu.val.val.val *
                contentEigenvalue d alpha.val.val mu.val.val.val)) /
        ((k + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) ∧
    (∀ alpha : PhysicalLower d k,
      (tensorMultiplicity d alpha.val : ℂ) =
        (∑ sigma : Equiv.Perm (Fin k), QAlgorithms.Schur.spechtCharacter alpha.val sigma⁻¹ *
          (d : ℂ) ^ cycleCount sigma) / (k.factorial : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
