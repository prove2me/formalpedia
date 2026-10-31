-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_linInterp_spectral_projector_regular
-- name    : QAlgorithms.Nannicini.linInterp_spectral_projector_regular
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-30T15:00:23.613228+00:00
-- url     : https://prove2.me/theorems/52a41066-10a2-45f4-ac47-0417ce510d1b
-- title:
--   Regularity of the spectral projector and reduced resolvent along a gapped linear interpolation
-- statement:
--   There is a universal constant $K_0$ with the following property. Let $H_I, H_F$ be Hermitian matrices on $\mathbb C^\iota$, let $D = H_F - H_I$, and let
--
--   $$H(s) = (1-s)H_I + sH_F, \qquad s\in[0,1].$$
--
--   Suppose $\lambda:[0,1]\to\mathbb R$ is continuous and, for every $s$, $\lambda(s)$ is a simple eigenvalue of $H(s)$ whose distance to the rest of the spectrum is at least $\gamma>0$. Let $P(s)$ be the orthogonal projector onto the eigenline of $\lambda(s)$ and $R(s) = (H(s)-\lambda(s))^{-1}(1-P(s))$ the reduced resolvent. Then $P$ and $R$ are differentiable on $[0,1]$, $P'$ is continuous, and
--
--   $$P' = -R\,D\,P - P\,D\,R, \qquad \|P\|\le 1,\quad \|R\|\le \frac1\gamma,\quad \|R'\|\le K_0\,\frac{\|D\|}{\gamma^2}$$
--
--   (operator norms), together with the algebraic identities $P^2=P$, $P^*=P$, $HP=\lambda P$, $(H-\lambda)R = 1-P$, $RP = PR = 0$, and every $\lambda(s)$-eigenvector being fixed by $P(s)$.
--
--   This is the first-order perturbation theory of an isolated eigenvalue (Kato) specialised to a linear path; it is the spectral input for the adiabatic theorem along linear interpolations (Corollary 9.24).
--
--   **Formalization note.** $P,P',R,R'$ are continuous $\mathbb C$-linear maps on `EuclideanSpace ℂ ι`, derivatives are `HasDerivWithinAt` on `Set.Icc 0 1`, the norm of $D$ is `specNorm`, and the spectral data are stated as the listed pointwise identities rather than by a definition of $P$.
-- source:
--   T. Kato, Perturbation Theory for Linear Operators, Ch. II §2; Jansen–Ruskai–Seiler, J. Math. Phys. 48 (2007) 102111; used for Nannicini, Quantum algorithms for optimizers (arXiv:2408.07086v5), Cor. 9.24.

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

universe u

namespace QAlgorithms.Nannicini

/-- Kato's perturbation theory for the gapped linear interpolation `H(s) = (1 − s)H_I + sH_F`,
`D = H_F − H_I`. If `λ(s)` is a continuous simple eigenvalue of `H(s)` with gap `γ > 0` on `[0, 1]`,
then the spectral projector `P(s)` and the reduced resolvent `R(s) = (H(s) − λ(s))⁻¹(1 − P(s))`
are differentiable on `[0, 1]`, with `P′` continuous, Kato's formula `P′ = −R D P − P D R`, and
`‖P‖ ≤ 1`, `‖R‖ ≤ 1/γ`, `‖R′‖ ≤ K₀‖D‖/γ²` for a universal constant `K₀`. -/
theorem linInterp_spectral_projector_regular : ∃ K0 : ℝ, ∀ {ι : Type u} [Fintype ι]
    [DecidableEq ι] (HI HF : Matrix ι ι ℂ), HI.IsHermitian → HF.IsHermitian →
    ∀ (lam : ℝ → ℝ), ContinuousOn lam (Set.Icc 0 1) →
    ∀ (γ : ℝ), 0 < γ →
    (∀ s ∈ Set.Icc (0 : ℝ) 1, HasGapAround (linInterp HI HF s) (lam s) γ) →
    ∃ P P' R R' : ℝ → (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι),
      ContinuousOn P' (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt P (P' s) (Set.Icc 0 1) s ∧
        HasDerivWithinAt R (R' s) (Set.Icc 0 1) s ∧
        (∀ x, P s (P s x) = P s x) ∧
        (∀ x y, inner ℂ (P s x) y = inner ℂ x (P s y)) ∧
        (∀ x, act (linInterp HI HF s) x = (lam s : ℂ) • x → P s x = x) ∧
        (∀ x, act (linInterp HI HF s) (P s x) = (lam s : ℂ) • P s x) ∧
        (∀ x, act (linInterp HI HF s) (R s x) - (lam s : ℂ) • R s x = x - P s x) ∧
        (∀ x, R s (P s x) = 0) ∧ (∀ x, P s (R s x) = 0) ∧
        (∀ x, P' s x = -R s (act (HF - HI) (P s x)) - P s (act (HF - HI) (R s x))) ∧
        ‖P s‖ ≤ 1 ∧ ‖R s‖ ≤ 1 / γ ∧ ‖R' s‖ ≤ K0 * specNorm (HF - HI) / γ ^ 2 := by
  sorry

end QAlgorithms.Nannicini
