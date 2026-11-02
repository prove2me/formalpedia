-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_boolean_quasipoint_generates_sector
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.boolean_quasipoint_generates_sector
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:51:19.741203+00:00
-- url     : https://prove2.me/theorems/59de2c66-8325-469d-a189-3643b30110b8
-- title:
--   Lemma 3.7
-- statement:
--   If a Boolean sector $S$ in a complete orthomodular lattice contains a Boolean quasipoint $\beta$, then
--
--   $$\langle\beta\rangle_{\mathrm{ortholattice}}=S.$$
--
--   **Source correction.** Generation uses finite meets, finite joins, the designated orthocomplement, and the bounds. The proof obtains an element from its complement; generation by finite meets and joins alone would not yield this assertion.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 69, Lemma 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Lemma 3.7; de Groote, Observables I, PDF p./pp. 69.
Source convention: Boolean sectors are maximal distributive sub-ortholattices; generation includes complements and bounds.
-/
theorem boolean_quasipoint_generates_sector {L : Type u} [CompleteLattice L] (perp : L → L) (horth : IsOrthomodular perp)
    (S : Set L) (hS : IsBooleanSector perp S)
    (B : Set L) (hB : IsBooleanQuasipoint perp B) (hBS : B ⊆ S) :
    ortholatticeGenerated perp B = S := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
