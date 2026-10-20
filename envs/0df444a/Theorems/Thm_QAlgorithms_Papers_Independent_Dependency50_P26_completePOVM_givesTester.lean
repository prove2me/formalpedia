-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_completePOVM_givesTester
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.completePOVM_givesTester
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:43:34.203917+00:00
-- url     : https://prove2.me/theorems/bddc9c40-2b17-4927-b8dc-9d5e55061e69
-- title:
--   Theorem 13: existence of informationally complete testers
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $N\ge1$, let $d_{\rm in}=\prod_{j=0}^{N-1}\dim H_{2j}$, and let $\{E_i\}$ be any finite informationally complete POVM on the external wire space. Then
--
--   $$
--   P_i=\frac{E_i}{d_{\rm in}}
--   $$
--
--   forms an informationally complete $N$-tester. Informational completeness means the complex span of the transposed effects is the full operator space. The source odd labels at this location are reindexed to the zero-based input labels used here.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 19, Theorem 13: existence of informationally complete testers

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF pp.19–20, Theorem 13: scale an arbitrary informationally complete POVM by the
product of input dimensions (odd source labels there are zero-based even labels here). -/
theorem completePOVM_givesTester (s : Signature) (n k : ℕ) (hn : 0 < n)
    (E : Fin k → Matrix (Basis s n) (Basis s n) ℂ)
    (hE : POVM E) (hic : InformationallyComplete E) :
    let P := fun i => (((inputDimension s n : ℕ) : ℂ)⁻¹) • E i
    CombTester s n k P ∧ InformationallyComplete P := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
