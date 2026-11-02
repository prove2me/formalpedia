-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_orthonormal_basis_unique_boolean_sector
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.orthonormal_basis_unique_boolean_sector
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:52:29.156171+00:00
-- url     : https://prove2.me/theorems/422d6ecb-8a2f-4b9a-86da-808eb844b6ae
-- title:
--   Proposition 3.26
-- statement:
--   Let $(e_k)_{k\in K}$ be an orthonormal basis of an arbitrary complex Hilbert space. There is a unique Boolean sector containing all basis lines, and it is the actual subset
--
--   $$S=\{U\in L(H):\forall k,\ e_k\in U\text{ or }e_k\in U^\perp\}.$$
--
--   Every line $\mathbb C e_k$ belongs to this sector. Sectors are maximal distributive sub-ortholattices. The zero-space, empty-basis case is retained.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 72, Proposition 3.26

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.26; de Groote, Observables I, PDF p./pp. 72.
Source convention: Boolean sectors are maximal distributive sub-ortholattices; generation includes complements and bounds.
-/
theorem orthonormal_basis_unique_boolean_sector {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type v} (e : HilbertBasis K ℂ H) :
    let S : Set (ClosedSubmodule ℂ H) := {U | ∀ k, e k ∈ U ∨ e k ∈ U.orthogonal}
    IsBooleanSector (fun U : ClosedSubmodule ℂ H => U.orthogonal) S ∧
    (∀ k, closedLine (e k) ∈ S) ∧
    ∀ T : Set (ClosedSubmodule ℂ H),
      IsBooleanSector (fun U : ClosedSubmodule ℂ H => U.orthogonal) T →
      (∀ k, closedLine (e k) ∈ T) → T = S := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
