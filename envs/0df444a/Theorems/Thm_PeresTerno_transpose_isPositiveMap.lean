-- Prove2me | Theorems.Thm_PeresTerno_transpose_isPositiveMap
-- name    : PeresTerno.transpose_isPositiveMap
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T08:55:49.481153+00:00
-- url     : https://prove2.me/theorems/47eb0b02-df01-42ca-ac39-466ba7cd4d7e
-- title:
--   Time reversal ($\rho\mapsto\rho^T$) is a positive map
-- statement:
--   For every finite index set $d$, the transposition map $\rho\mapsto\rho^{T}$ on complex $d\times d$ matrices is positive: if $\rho$ is positive semidefinite then so is $\rho^{T}$.
--
--   The source states this for complex conjugation of $\rho$, interpreted as time reversal; on Hermitian matrices complex conjugation and transposition coincide.
--
--   **Formalization Note** Time reversal is encoded as the $\mathbb C$-linear transposition map, which agrees with entrywise complex conjugation on every Hermitian matrix. The linear form is the one for which complete positivity (next milestone) is meaningful.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, "complex conjugation of rho (whose meaning is time reversal) is a positive map"

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem transpose_isPositiveMap {d : Type*} [Fintype d] :
    IsPositiveMap (fun ρ : Matrix d d ℂ => ρᵀ) := by
  sorry

end PeresTerno
