-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P28_fidelityStrictUpperBound
-- name    : QAlgorithms.Papers.Independent.Extend50.P28.fidelityStrictUpperBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:21:40.157516+00:00
-- url     : https://prove2.me/theorems/82311a66-c34b-488e-9b4a-72417feea994
-- title:
--   Representation-sensitive strict finite-size fidelity bound
-- statement:
--   Let $n,d\ge2$, let $H=(\mathbb C^d)^{\otimes n}$ with its fixed computational orthonormal basis, and put $N=n-1$. For $a=1,\ldots,N$, let $T_a$ be the last-factor partial transpose of the tensor permutation swapping $a$ and $n$, and put $\rho=\sum_aT_a$. Write $d_\eta$ for the actual Specht dimension and $m_\eta$ for the multiplicity of that Specht module in the appropriate tensor permutation representation; these are defined by dimensions of actual intertwiner spaces. Put $\sigma_a=d^{-N}T_a$ and $\widetilde\rho=\sum_a\sigma_a$. The standard deterministic PBT entanglement fidelity for $N$ normalized maximally entangled resource pairs and the completed square-root measurement is the computed quantity $F_n(d)=d^{-2}\sum_a\operatorname{Tr}(\sigma_a\widetilde\rho^{-1/2}\sigma_a\widetilde\rho^{-1/2})$. Every inverse half-power is the spectral support inverse, equal to zero on the kernel. For each size n-1 shape $\nu$ with $h(\nu)<d$, let $M_\nu$ count actual second-kind copies, using physical intertwiner spaces annihilated by all moving-last-letter generators. Then
--
--   $$
--   F_n(d)\le1-\frac{1}{d^n}\sum_{h(\nu)<d}M_\nu d_\nu<1.
--   $$
--
--   The representation-sensitive correction and strictness are both included; M_nu is neither supplied as arbitrary data nor defined by the erroneous (25).
-- source:
--   Simplified formalism of the algebra of partially transposed permutation operators with applications, arXiv:1708.02434v2, PDF p. 27, Section 5.4 unnumbered

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P28

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

local notation "Shape" => (fun k : ℕ => QAlgorithms.Schur.Partition k k)

local notation "Word" => (fun d n : ℕ => Fin n → Fin d)

/-- PDF p.27, Eq.(143), with n=N+1: the representation-sensitive upper
bound and its strict finite-size inequality. M is actual second-kind multiplicity,
not the erroneous printed expression (25), and no bound is built into fidelity. -/
theorem fidelityStrictUpperBound (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    pbtFidelity d N ≤
      1 - (∑ nu : SecondShapes d N,
        (secondKindMultiplicity d nu.val : ℝ) * (irrepDim nu.val : ℝ)) / (d : ℝ) ^ (N + 1) ∧
    1 - (∑ nu : SecondShapes d N,
      (secondKindMultiplicity d nu.val : ℝ) * (irrepDim nu.val : ℝ)) / (d : ℝ) ^ (N + 1) < 1 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P28

end
