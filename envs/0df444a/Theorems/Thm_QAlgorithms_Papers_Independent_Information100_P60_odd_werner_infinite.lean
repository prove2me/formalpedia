-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P60_odd_werner_infinite
-- name    : QAlgorithms.Papers.Independent.Information100.P60.odd_werner_infinite
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:46:46.927534+00:00
-- url     : https://prove2.me/theorems/946c959b-d214-4092-8a5e-e9e798cb89e3
-- title:
--   Theorem 8: infinite memory-assisted exponent and all full-Schmidt-rank pure optimizers
-- statement:
--   Let $\mathrm{MU}_d$ be the finite convex mixtures of unitary conjugations on $\mathbb C^d$. Write $E_{r,k}^c(\mathcal N)$ for the operational parallel block-i.i.d. Stein exponent against this composite i.i.d. null class, in bits, with a uniform Type-I constraint, local reference dimension $r$, and the zero-error outer limit taken after the block-count liminf and limsup. The value $r=1$ means no memory and $r=d$ supplies sufficient memory. Let $d\ge3$ be odd, and let the CPTP map $\mathcal N$ be unitarily equivalent to $\mathcal N_{WH}(X)=(\operatorname{Tr}(X)I-X^T)/(d-1)$. Then $$E_{d,1}^{\mathrm{unrestricted}}(\mathcal N)=\infty.$$ Every normalized pure state $|\psi\rangle\in\mathbb C^d\otimes\mathbb C^d$ whose coefficient matrix has nonzero determinant attains this value: $$\inf_{\Phi\in\mathrm{MU}_d}D((\operatorname{id}_d\otimes\Phi)(|\psi\rangle\langle\psi|)\Vert(\operatorname{id}_d\otimes\mathcal N)(|\psi\rangle\langle\psi|))=\infty.$$ Nonzero determinant is full Schmidt rank. This retains all optimizers, without a finite-shot perfect-discrimination claim.
-- source:
--   Quantum hypothesis testing of non-mixed-unitarity: A multifaceted hierarchy of quantum channel discrimination, arXiv:2609.40355v1, PDF p. 33, Theorem 8: infinite memory-assisted exponent and all full-Schmidt-rank pure optimizers

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv-2609.40355v1, PDF pp.33–34, Theorem 8, including every full-Schmidt-rank optimizer. -/
theorem odd_werner_infinite (d : ℕ) (hd : 3 ≤ d) (ho : Odd d) (N : Maps d d)
    (hN : IsChannel N) (he : UnitaryEquivalent (wernerHolevo d) N) :
    blockExponent d (MU d) N 1 .unrestricted = ⊤ ∧
    ∀ psi : EuclideanSpace ℂ (Fin d × Fin d), ‖psi‖ = 1 →
      (Matrix.of fun i j => psi (i,j)).det ≠ 0 → singleValue N (pureDensity psi) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Information100.P60

end
