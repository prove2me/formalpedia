-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_atom_principal_is_quasipoint
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.atom_principal_is_quasipoint
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T16:34:13.850016+00:00
-- url     : https://prove2.me/theorems/e1ad75e1-ed42-48c7-b60c-3b7e0f48f80f
-- title:
--   The principal upper set of an atom is a quasipoint
-- statement:
--   Let $L$ be a bounded lattice and let $a$ be an atom, meaning $a\ne0$ and there is no element strictly between $0$ and $a$. Then
--
--   $$B_a=\{b\in L:a\le b\}$$
--
--   is a quasipoint of L: a maximal proper nonempty directed filter base. This identifies atomic lattice elements with principal quasipoints and supports the characterization of isolated points of Stone spectra. Orthomodularity is not needed for this direction.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Proposition 3.6 and proof, printed p.43 (PDF p.44), equation (3.3) and the final sentence of the proof.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

namespace QAlgorithms.Papers.Independent.Intakethird100.P20
theorem atom_principal_is_quasipoint {L : Type*} [Lattice L] [BoundedOrder L]
    (a : L) (ha : IsAtom a) : IsQuasipoint (principalQuasipoint a) := by sorry
end QAlgorithms.Papers.Independent.Intakethird100.P20
