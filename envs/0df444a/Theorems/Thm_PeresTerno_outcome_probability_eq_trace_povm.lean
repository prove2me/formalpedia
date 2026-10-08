-- Prove2me | Theorems.Thm_PeresTerno_outcome_probability_eq_trace_povm
-- name    : PeresTerno.outcome_probability_eq_trace_povm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T00:14:51.547334+00:00
-- url     : https://prove2.me/theorems/ea59a541-c02e-4638-90dc-73ac0e1bab16
-- title:
--   Eq. (7): $\sum_m \mathrm{tr}(A_m\rho A_m^\dagger) = \mathrm{tr}(\rho E)$
-- statement:
--   Let $\{A_m\}_{m\in I}$ be a finite family of complex $e\times d$ matrices (the Kraus matrices of one outcome $\mu$), let $E = \sum_m A_m^\dagger A_m$ be the corresponding POVM element, and let $\rho$ be any complex $d\times d$ matrix. Then
--   $$\sum_{m\in I} \operatorname{tr}\big(A_m\,\rho\,A_m^\dagger\big) = \operatorname{tr}(\rho\,E).$$
--
--   This is Eq. (7) of the source: the probability of outcome $\mu$ depends on the Kraus matrices only through the POVM element $E_\mu$.
--
--   **Formalization Note** The identity is stated for every square matrix $\rho$, which contains the source's case of a density matrix.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, Eq. (7) (with Eq. (8))

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem outcome_probability_eq_trace_povm {d e ι : Type*} [Fintype d] [Fintype e] [Fintype ι]
    (A : ι → Matrix e d ℂ) (ρ : Matrix d d ℂ) :
    ∑ m, trace (A m * ρ * (A m)ᴴ) = trace (ρ * povmElement A) := by
  sorry

end PeresTerno
