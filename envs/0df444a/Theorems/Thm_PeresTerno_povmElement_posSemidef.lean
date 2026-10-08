-- Prove2me | Theorems.Thm_PeresTerno_povmElement_posSemidef
-- name    : PeresTerno.povmElement_posSemidef
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T00:39:18.559011+00:00
-- url     : https://prove2.me/theorems/d663bc71-3cc3-4c36-84b5-752aacd8d7b5
-- title:
--   Eq. (8): POVM elements $E=\sum_m A_m^\dagger A_m$ are positive
-- statement:
--   Let $\{A_m\}_{m\in I}$ be a finite family of complex $e\times d$ matrices. Then the $d\times d$ matrix
--   $$E = \sum_{m\in I} A_m^\dagger A_m$$
--   is positive semidefinite.
--
--   The source calls the matrices of Eq. (8) "the positive operators $E_\mu$"; this is the positivity that makes them elements of a POVM.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, Eq. (8) ("The positive operators E_mu")

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem povmElement_posSemidef {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) :
    (povmElement A).PosSemidef := by
  sorry

end PeresTerno
