-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_open_atom_iff_singleton
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.open_atom_iff_singleton
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T16:43:02.60698+00:00
-- url     : https://prove2.me/theorems/fad57ed3-c781-4429-b8d6-b3ac52d3101d
-- title:
--   Atoms of the open-set lattice are open singletons in a T1 space
-- statement:
--   Let $M$ be a $T_1$ topological space and let $U$ be an open subset. Then
--
--   $$U\text{ is an atom of }\mathcal O(M)\quad\Longleftrightarrow\quad\exists x\in M,\ U=\{x\}.$$
--
--   Here an atom is a nonempty open set with no strictly smaller nonempty open subset. The singleton is automatically open, so its point is isolated. This is the lattice-to-space step in the description of atomic open quasipoints; the T1 separation condition suffices.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Proposition 3.6 and the paragraph following it, printed pp.43–44 (PDF pp.44–45), atomic quasipoints of the lattice of opens. This supporting lemma weakens Hausdorff separation to T1.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20
open Set TopologicalSpace

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem open_atom_iff_singleton {M : Type*} [TopologicalSpace M] [T1Space M]
    (U : TopologicalSpace.Opens M) : IsAtom U ↔ ∃ x : M, (U : Set M) = {x} := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
