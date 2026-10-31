-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_eigvec_eq_smul_of_hasGapAround
-- name    : QAlgorithms.Nannicini.eigvec_eq_smul_of_hasGapAround
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-30T14:19:56.315615+00:00
-- url     : https://prove2.me/theorems/be4fbe3a-49d4-40f3-925b-ac265ba09eed
-- title:
--   Unit eigenvectors of a simple eigenvalue agree up to a phase
-- statement:
--   Let $A$ be Hermitian and $\lambda$ an eigenvalue of $A$ of multiplicity one (as encoded by HasGapAround $A$ $\lambda$ $\gamma$). If $x,y$ are unit vectors with $Ax=\lambda x$, $Ay=\lambda y$, then $y=\omega x$ for some $\omega\in\mathbb C$ with $|\omega|=1$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5, §9.2 (proof of Corollary 9.24); cf. Jansen–Ruskai–Seiler, J. Math. Phys. 48 (2007) 102111, and Kato, J. Phys. Soc. Japan 5 (1950). https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- If `λ` is a simple eigenvalue of the Hermitian matrix `A` (`HasGapAround A λ γ`), any two
unit eigenvectors for `λ` differ by a unit complex scalar. -/
theorem eigvec_eq_smul_of_hasGapAround {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (lam γ : ℝ) (hA : HasGapAround A lam γ) (x y : EuclideanSpace ℂ ι)
    (hx : IsState x) (hy : IsState y) (hAx : act A x = (lam : ℂ) • x)
    (hAy : act A y = (lam : ℂ) • y) : ∃ ω : ℂ, ‖ω‖ = 1 ∧ y = ω • x := by
  sorry

end QAlgorithms.Nannicini
