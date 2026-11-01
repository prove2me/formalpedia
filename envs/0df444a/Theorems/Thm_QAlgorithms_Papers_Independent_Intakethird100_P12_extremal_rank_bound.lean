-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P12_extremal_rank_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P12.extremal_rank_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:49:22.636205+00:00
-- url     : https://prove2.me/theorems/f10e726c-e1f0-45d5-a3fb-475aabd6d01c
-- title:
--   Unnumbered Corollary: extremal rank bound
-- statement:
--   Let $d_1,d_2$ be the dimensions of finite-dimensional complex Hilbert spaces with chosen orthonormal bases. Let $\rho_1,\rho_2$ be positive semidefinite operators of trace one. Write $C(\rho_1,\rho_2)$ for all joint density matrices with these two partial traces, and $E(\rho_1,\rho_2)$ for its extreme points over the real scalars. Coordinates in the tensor product use lexicographic order.
--
--   For every extreme coupling $\rho\in E(\rho_1,\rho_2)$,
--   $$\operatorname{rank}\rho\le\sqrt{d_1^2+d_2^2-1}.$$
--   This bounds the rank of an extreme point using only the subsystem dimensions. One-dimensional subsystems are included; no full-rank assumption is imposed on the marginals.
-- source:
--   Extremal Quantum States in Coupled Systems, arXiv:quant-ph/0307182v1, PDF p. 6, Unnumbered Corollary after Proposition 2.3: rank bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P12

namespace QAlgorithms.Papers.Independent.Intakethird100.P12

open scoped ComplexConjugate ComplexOrder

/-- Unnumbered Corollary after Proposition 2.3, PDF pp.6–7.
No d1,d2>=2 restriction: singleton coupling sets also satisfy the bound. -/
theorem extremal_rank_bound {d1 d2 : ℕ}
    (rho1 : Matrix (Fin d1) (Fin d1) ℂ) (rho2 : Matrix (Fin d2) (Fin d2) ℂ)
    (hm1 : IsDensityMatrix rho1) (hm2 : IsDensityMatrix rho2)
    (rho : Matrix (Fin d1 × Fin d2) (Fin d1 × Fin d2) ℂ)
    (hext : rho ∈ Set.extremePoints ℝ (finiteCouplingSet rho1 rho2)) :
    (rho.rank : ℝ) ≤ Real.sqrt ((d1 : ℝ)^2 + (d2 : ℝ)^2 - 1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P12
