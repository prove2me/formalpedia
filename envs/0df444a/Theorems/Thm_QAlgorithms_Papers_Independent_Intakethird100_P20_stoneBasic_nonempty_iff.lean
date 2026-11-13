-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_stoneBasic_nonempty_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.stoneBasic_nonempty_iff
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-12T16:08:52.757192+00:00
-- url     : https://prove2.me/theorems/5ceab424-742e-4b58-8adf-945be6eaf02c
-- title:
--   A Stone basic open is nonempty exactly when its element is nonzero
-- statement:
--   Let $L$ be a bounded lattice and let $Q_a$ be the set of quasipoints containing $a$. Then
--
--   $$Q_a\ne\varnothing\quad\Longleftrightarrow\quad a\ne0.$$
--
--   This identifies nonzero lattice elements with nonempty basic neighborhoods. It is a supporting lemma for the characterization of closures of unions of Stone basic sets.
-- source:
--   H. F. de Groote, Observables I: Stone Spectra, arXiv:math-ph/0509020v1, https://arxiv.org/pdf/math-ph/0509020v1, Section 3.1, printed pp.38–39 (Zorn extension and the definition of Q_a); Section 3.2, printed p.44, the equivalence immediately before Proposition 3.7.

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

theorem stoneBasic_nonempty_iff {L : Type*} [Lattice L] [BoundedOrder L] (a : L) :
    (stoneBasic a).Nonempty ↔ a ≠ ⊥ := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20
