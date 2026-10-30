-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_fidelityLowerBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.fidelityLowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:22:14.42299+00:00
-- url     : https://prove2.me/theorems/920ebbc2-1f62-4c04-91d4-9bbdd7dfe72c
-- title:
--   Exact finite-size lower fidelity bound
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Put $\sigma_a=d^{-N}T_a$ and $\widetilde\rho=\sum_a\sigma_a$. The standard deterministic PBT entanglement fidelity for $N$ normalized maximally entangled resource pairs and the completed square-root measurement is the computed quantity $F_n(d)=d^{-2}\sum_a\operatorname{Tr}(\sigma_a\widetilde\rho^{-1/2}\sigma_a\widetilde\rho^{-1/2})$. Every inverse half-power is the spectral support inverse, equal to zero on the kernel.
--
--   $$
--   F_n(d)\ge\frac{n-1}{d^2+n-2}.
--   $$
--
--   This is the non-asymptotic result rederived here by a different method and explicitly credited to Beigi–König [2].
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 28, Section 5.4 unnumbered main result

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.28, Eq.(152): exact non-asymptotic lower bound, with the port
convention N=n-1. This paper rederives the result credited to Beigi–König [2]. -/
theorem fidelityLowerBound (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    ((n : ℝ) - 1) / ((d : ℝ) ^ 2 + n - 2) ≤ pbtFidelity d (n - 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
