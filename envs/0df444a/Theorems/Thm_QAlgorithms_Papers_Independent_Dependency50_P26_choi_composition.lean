-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_choi_composition
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.choi_composition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:28:36.358919+00:00
-- url     : https://prove2.me/theorems/f497fcd5-71be-486e-801d-3cf07bbafa36
-- title:
--   Theorem 1 (Composition rules)
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $\mathcal M:L(H_0)\to L(H_1)$ and $\mathcal N:L(H_1)\to L(H_2)$ be complex-linear. Link their output-first Choi operators along $H_1$, using the partial transpose in the fixed basis. Then
--
--   $$
--   C(\mathcal N\circ\mathcal M)=C(\mathcal N)*C(\mathcal M).
--   $$
--
--   This composition identity requires neither positivity nor trace preservation.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 3, Theorem 1 (Composition rules)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.3, Theorem 1. The printed name M for the composite is corrected to C=N∘M. -/
theorem choi_composition {I J O : Type*} [Fintype I] [Fintype J] [Fintype O]
    [Nonempty I] [Nonempty J] [Nonempty O]
    (M : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (N : Matrix J J ℂ →ₗ[ℂ] Matrix O O ℂ) :
    outputFirstChoi (N.comp M) = channelLink (outputFirstChoi N) (outputFirstChoi M) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
