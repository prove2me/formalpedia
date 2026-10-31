-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_kato_projector_regular_of_affine
-- name    : QAlgorithms.Nannicini.kato_projector_regular_of_affine
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-30T15:47:54.990258+00:00
-- url     : https://prove2.me/theorems/a509ca83-92ce-4eca-ae66-be2d2ce7d712
-- title:
--   Kato's formula for the spectral projector along an affine operator family
-- statement:
--   Let $E$ be a complex inner product space, $S\subseteq\mathbb{R}$, and $H:\mathbb{R}\to\mathcal{L}(E)$ an affine family of bounded operators, $H(t)=H(s)+(t-s)D$. Let $\lambda:\mathbb{R}\to\mathbb{R}$ be continuous on $S$, $\gamma>0$, and $P,R:\mathbb{R}\to\mathcal{L}(E)$ such that for every $s\in S$
--   $$(H(s)-\lambda(s))P(s)=P(s)(H(s)-\lambda(s))=0,\qquad (H(s)-\lambda(s))R(s)=R(s)(H(s)-\lambda(s))=1-P(s),$$
--   $$R(s)P(s)=P(s)R(s)=0,\qquad \|P(s)\|\le 1,\qquad \|R(s)\|\le 1/\gamma,$$
--   and $P(s)x=x$ for some unit vector $x$. Then for every $s\in S$, $P$ is differentiable within $S$ at $s$ with Kato's formula
--   $$P'(s)=-R(s)DP(s)-P(s)DR(s),$$
--   and $R$ is differentiable within $S$ at $s$ with $\|R'(s)\|\le 6\|D\|/\gamma^2$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5, §9.2 (proof of Corollary 9.24); cf. T. Kato, Perturbation Theory for Linear Operators (1966), Ch. II §5, and Jansen–Ruskai–Seiler, J. Math. Phys. 48 (2007) 102111. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Abstract Kato regularity along an affine family. Let `H(t) = H(s) + (t − s)D` be an affine
family of operators on a complex inner product space, `λ` continuous on `S ⊆ ℝ`, and `P(s)`, `R(s)`
satisfying the algebraic relations of the spectral projector and reduced resolvent of `H(s)` at `λ(s)`
(`(H − λ)P = P(H − λ) = 0`, `(H − λ)R = R(H − λ) = 1 − P`, `RP = PR = 0`), with `‖P‖ ≤ 1`,
`‖R‖ ≤ 1/γ` and `P(s)` fixing a unit vector. Then `P` is differentiable within `S` with Kato's formula
`P′ = −RDP − PDR`, and `R` is differentiable within `S` with `‖R′‖ ≤ 6‖D‖/γ²`. -/
theorem kato_projector_regular_of_affine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Set ℝ) (H : ℝ → E →L[ℂ] E) (D : E →L[ℂ] E)
    (hH : ∀ s t, H t = H s + ((t - s : ℝ) : ℂ) • D)
    (lam : ℝ → ℝ) (hlam : ContinuousOn lam S) (γ : ℝ) (hγ : 0 < γ)
    (P R : ℝ → E →L[ℂ] E)
    (hGP : ∀ s ∈ S, (H s - (lam s : ℂ) • 1) * P s = 0)
    (hPG : ∀ s ∈ S, P s * (H s - (lam s : ℂ) • 1) = 0)
    (hGR : ∀ s ∈ S, (H s - (lam s : ℂ) • 1) * R s = 1 - P s)
    (hRG : ∀ s ∈ S, R s * (H s - (lam s : ℂ) • 1) = 1 - P s)
    (hRP : ∀ s ∈ S, R s * P s = 0) (hPR : ∀ s ∈ S, P s * R s = 0)
    (hPn : ∀ s ∈ S, ‖P s‖ ≤ 1) (hRn : ∀ s ∈ S, ‖R s‖ ≤ 1 / γ)
    (hx : ∀ s ∈ S, ∃ x : E, ‖x‖ = 1 ∧ P s x = x) :
    ∃ R' : ℝ → E →L[ℂ] E, ∀ s ∈ S,
      HasDerivWithinAt P (-(R s * D * P s) - P s * D * R s) S s ∧
      HasDerivWithinAt R (R' s) S s ∧ ‖R' s‖ ≤ 6 * ‖D‖ / γ ^ 2 := by
  sorry

end QAlgorithms.Nannicini
