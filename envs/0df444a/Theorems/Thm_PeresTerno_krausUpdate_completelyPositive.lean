-- Prove2me | Theorems.Thm_PeresTerno_krausUpdate_completelyPositive
-- name    : PeresTerno.krausUpdate_completelyPositive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T02:11:27.685482+00:00
-- url     : https://prove2.me/theorems/8e766928-d271-416a-a29f-a1c607822cf0
-- title:
--   Eq. (6) is a completely positive map
-- statement:
--   Let $\{A_m\}_{m\in I}$ be a finite family of complex $e\times d$ matrices and let $T(\rho) = \sum_m A_m\rho A_m^\dagger$. Then $T$ is completely positive: for every $n\in\mathbb N$ and every positive semidefinite matrix $R$ on $\mathbb C^d\otimes\mathbb C^n$, the matrix $(T\otimes\mathbb 1_n)(R)$ is positive semidefinite.
--
--   This is the "Kraus maps are completely positive" half of the source's statement that Eq. (6) is the most general completely positive linear map.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, paragraph after Eq. (6) ("Eq. (6) is the most general completely positive linear map")

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem krausUpdate_completelyPositive {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) :
    IsCompletelyPositive (krausUpdate A) := by
  sorry

end PeresTerno
