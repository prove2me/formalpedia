-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_theorem52
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.theorem52
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:17:22.184054+00:00
-- url     : https://prove2.me/theorems/27b287fa-69e2-4a83-a5d3-945cdeb82759
-- title:
--   Standard PBT fidelity bound and fixed-dimension convergence
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Put $\sigma_a=d^{-N}T_a$ and $\widetilde\rho=\sum_a\sigma_a$. The standard deterministic PBT entanglement fidelity for $N$ normalized maximally entangled resource pairs and the completed square-root measurement is the computed quantity $F_n(d)=d^{-2}\sum_a\operatorname{Tr}(\sigma_a\widetilde\rho^{-1/2}\sigma_a\widetilde\rho^{-1/2})$. Every inverse half-power is the spectral support inverse, equal to zero on the kernel. For every fixed integer $d\ge2$,
--
--   $$
--   F_n(d)\le1\quad(n\ge2),\qquad \lim_{n\to\infty}F_n(d)=1.
--   $$
--
--   Both conclusions are about the defined trace functional, with a pointwise limit at fixed d; no uniform convergence in d is asserted.
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 24, Theorem 52

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.24, Theorem 52, Eq.(122): both the bound and convergence at each
fixed local dimension. Fidelity is computed from the actual signals, never supplied. -/
theorem theorem52 (d : ℕ) (hd : 2 ≤ d) :
    (∀ n : ℕ, 2 ≤ n → pbtFidelity d (n - 1) ≤ 1) ∧
    Filter.Tendsto (fun n : ℕ => pbtFidelity d (n - 1)) Filter.atTop (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
