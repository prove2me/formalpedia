-- Prove2me | Theorems.Thm_PeresTerno_completelyPositive_exists_kraus
-- name    : PeresTerno.completelyPositive_exists_kraus
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-05T02:34:24.70977+00:00
-- url     : https://prove2.me/theorems/13de0e91-0a77-4859-a807-4d82114a62f0
-- title:
--   Eq. (6) is the most general completely positive linear map (Kraus representation)
-- statement:
--   Let $d$ and $e$ be finite index sets and let $T$ be a $\mathbb C$-linear map from complex $d\times d$ matrices to complex $e\times e$ matrices. If $T$ is completely positive, then there exist $N\in\mathbb N$ and complex $e\times d$ matrices $A_1,\dots,A_N$ such that
--   $$T(\rho) = \sum_{k=1}^{N} A_k\,\rho\,A_k^\dagger \qquad\text{for every } \rho .$$
--
--   Together with the complete positivity of Kraus maps, this is the source's statement that Eq. (6) is the most general completely positive linear map (the Kraus/Choi representation theorem).
-- source:
--   A. Peres and D. R. Terno, Quantum information and relativity theory, Rev. Mod. Phys. 76, 93-123 (2004), https://doi.org/10.1103/RevModPhys.76.93, p. 100, Sec. II.D, "Eq. (6) is the most general completely positive linear map (Stinespring, 1955; Davies, 1976; Kraus, 1983)"

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics

open Matrix
open scoped ComplexOrder

namespace PeresTerno

theorem completelyPositive_exists_kraus {d e : Type*} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e]
    (T : Matrix d d ℂ →ₗ[ℂ] Matrix e e ℂ) (hT : IsCompletelyPositive T) :
    ∃ (N : ℕ) (A : Fin N → Matrix e d ℂ), ∀ ρ, T ρ = krausUpdate A ρ := by
  sorry

end PeresTerno
