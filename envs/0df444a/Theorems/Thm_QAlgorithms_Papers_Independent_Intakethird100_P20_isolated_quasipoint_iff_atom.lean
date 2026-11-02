-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_isolated_quasipoint_iff_atom
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.isolated_quasipoint_iff_atom
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:39:15.628203+00:00
-- url     : https://prove2.me/theorems/4d716854-bb5b-4ec1-9e53-40ea2e8a0b97
-- title:
--   Proposition 3.6
-- statement:
--   For an orthomodular lattice $L$, a quasipoint $\mathfrak B$ is isolated in the Stone topology if and only if there is a unique order-theoretic atom $a_0$ with
--
--   $$\mathfrak B=\{a\in L:a_0\le a\}.$$
--
--   An arbitrary generator of a principal proper filter does not suffice; it must be an atom.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 44, Proposition 3.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.6; de Groote, Observables I, PDF p./pp. 44.
-/
theorem isolated_quasipoint_iff_atom {L : Type u} [Lattice L] [BoundedOrder L] (perp : L → L)
    (horth : IsOrthomodular perp) (B : StoneSpectrum L) :
    IsOpen ({B} : Set (StoneSpectrum L)) ↔
      ∃! a : L, IsAtom a ∧ B.val = principalQuasipoint a := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
