-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_gapped_spectral_data
-- name    : QAlgorithms.Nannicini.gapped_spectral_data
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-30T15:47:56.964991+00:00
-- url     : https://prove2.me/theorems/8e0e9afb-b512-4bd4-be27-bf1022167036
-- title:
--   Spectral projector and reduced resolvent at a gapped simple eigenvalue
-- statement:
--   Let $A$ be a Hermitian matrix on $\mathbb{C}^n$ and let $\lambda$ be an eigenvalue of $A$ of multiplicity one, with every other eigenvalue $\mu$ satisfying $|\mu-\lambda|\ge\gamma>0$. Then there are linear operators $P$ and $R$ on $\mathbb{C}^n$ (the spectral projector and the reduced resolvent $R=(A-\lambda)^{-1}(1-P)$) such that
--   $$P^2=P,\quad P^*=P,\quad AP=PA=\lambda P,\quad (A-\lambda)R=R(A-\lambda)=1-P,\quad RP=PR=0,$$
--   $$\|P\|\le 1,\qquad \|R\|\le \frac{1}{\gamma},$$
--   and $Px=x$ for some unit vector $x$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5, §9.2 (proof of Corollary 9.24); cf. T. Kato, Perturbation Theory for Linear Operators (1966), Ch. II §5, and Jansen–Ruskai–Seiler, J. Math. Phys. 48 (2007) 102111. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Spectral data at a simple isolated eigenvalue. If `A` is Hermitian and `λ` is a simple
eigenvalue of `A` separated from the rest of the spectrum by `γ > 0` (`HasGapAround A λ γ`), there are
the orthogonal projector `P` onto the `λ`-eigenspace and the reduced resolvent
`R = (A − λ)⁻¹(1 − P)`: `P` is a self-adjoint idempotent commuting with `A` with range in the
eigenspace, `(A − λ)R = R(A − λ) = 1 − P`, `RP = PR = 0`, `‖P‖ ≤ 1`, `‖R‖ ≤ 1/γ`, and `P` fixes a unit
vector. -/
theorem gapped_spectral_data {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (lam γ : ℝ)
    (hγ : 0 < γ) (hA : HasGapAround A lam γ) :
    ∃ P R : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι,
      (∀ x, P (P x) = P x) ∧
      (∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) ∧
      (∀ x, act A (P x) = (lam : ℂ) • P x) ∧
      (∀ x, P (act A x) = (lam : ℂ) • P x) ∧
      (∀ x, act A (R x) - (lam : ℂ) • R x = x - P x) ∧
      (∀ x, R (act A x) - (lam : ℂ) • R x = x - P x) ∧
      (∀ x, R (P x) = 0) ∧ (∀ x, P (R x) = 0) ∧
      ‖P‖ ≤ 1 ∧ ‖R‖ ≤ 1 / γ ∧ (∃ x, ‖x‖ = 1 ∧ P x = x) := by
  sorry

end QAlgorithms.Nannicini
