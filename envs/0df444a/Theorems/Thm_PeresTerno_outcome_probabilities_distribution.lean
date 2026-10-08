-- Prove2me | Theorems.Thm_PeresTerno_outcome_probabilities_distribution
-- name    : PeresTerno.outcome_probabilities_distribution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-05T01:40:53.843844+00:00
-- url     : https://prove2.me/theorems/41d5b02e-6e2c-47f5-a947-a8f1bf55f94f
-- title:
--   Eqs. (7)-(8): outcome probabilities $p_\mu=\mathrm{tr}\,\rho'_\mu$ form a probability distribution
-- statement:
--   Let $\rho$ be a $d\times d$ density matrix, and for each outcome $\mu$ in a finite set $M$ let $\{A_{\mu m}\}_{m\in I_\mu}$ be a finite family of complex $e\times d$ Kraus matrices whose POVM elements are complete:
--   $$\sum_{\mu\in M} \sum_{m\in I_\mu} A_{\mu m}^\dagger A_{\mu m} = \mathbb 1_d .$$
--   Let $\rho'_\mu = \sum_m A_{\mu m}\rho A_{\mu m}^\dagger$ and $p_\mu = \operatorname{tr}\rho'_\mu$. Then
--
--   1. every $p_\mu$ is a nonnegative real number, and
--   2. $\sum_{\mu\in M} p_\mu = 1$.
--
--   This is the statement in the source that "the trace of $\rho'_\mu$ is the probability of occurrence of outcome $\mu$", made precise.
--
--   **Formalization Note** Probabilities are complex numbers here; "$p_\mu\ge 0$" uses the standard partial order on $\mathbb C$, meaning $p_\mu$ is real and nonnegative.
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, text after Eq. (6) and Eqs. (7)-(8)

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem outcome_probabilities_distribution {d e α : Type*} [Fintype d] [Fintype e] [Fintype α]
    {ι : α → Type*} [∀ μ, Fintype (ι μ)] [DecidableEq d]
    (A : ∀ μ, ι μ → Matrix e d ℂ) (hA : ∑ μ, povmElement (A μ) = 1)
    (ρ : Matrix d d ℂ) (hρ : IsDensityMatrix ρ) :
    (∀ μ, 0 ≤ trace (krausUpdate (A μ) ρ)) ∧ ∑ μ, trace (krausUpdate (A μ) ρ) = 1 := by
  sorry

end PeresTerno
