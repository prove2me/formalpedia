-- Prove2me | Theorems.Thm_PeresTerno_commuting_kraus_sum_eq_trace_povm
-- name    : PeresTerno.commuting_kraus_sum_eq_trace_povm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T10:26:46.122596+00:00
-- url     : https://prove2.me/theorems/b5846aa0-1d6f-453a-81aa-8ecb55dc53a1
-- title:
--   Sec. II.E: commuting Kraus matrices reduce Bob's term to $\mathrm{tr}(E_\mu\,\cdot)$
-- statement:
--   Let $\{A_m\}_{m\in I}$ and $\{B_n\}_{n\in J}$ be finite families of complex $d\times d$ matrices with $A_m B_n = B_n A_m$ for all $m,n$, and let $\rho$ be any $d\times d$ matrix. Then
--   $$\operatorname{tr}\Big(\sum_{m\in I}\sum_{n\in J} B_n A_m\,\rho\,A_m^\dagger B_n^\dagger\Big) = \operatorname{tr}\Big(E \sum_{n\in J} B_n\,\rho\,B_n^\dagger\Big),\qquad E = \sum_{m\in I}A_m^\dagger A_m .$$
--
--   This is the step in the source's derivation of Eq. (11): using Eq. (9) to exchange $A_{\mu m}$ and $B_{\nu n}$ (and their adjoints) and moving $A_{\mu m}$ cyclically, one obtains "expressions like Eq. (8)".
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, pp. 100-101, Sec. II.E, step from Eq. (10) to Eq. (11)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem commuting_kraus_sum_eq_trace_povm {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
    (A : ι → Matrix d d ℂ) (B : κ → Matrix d d ℂ)
    (hAB : ∀ m n, Commute (A m) (B n)) (ρ : Matrix d d ℂ) :
    trace (∑ m, ∑ n, B n * A m * ρ * (A m)ᴴ * (B n)ᴴ)
      = trace (povmElement A * ∑ n, B n * ρ * (B n)ᴴ) := by
  sorry

end PeresTerno
