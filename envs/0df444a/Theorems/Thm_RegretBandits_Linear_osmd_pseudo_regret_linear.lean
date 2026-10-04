-- Prove2me | Theorems.Thm_RegretBandits_Linear_osmd_pseudo_regret_linear
-- name    : RegretBandits.Linear.osmd_pseudo_regret_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:33:32.264098+00:00
-- url     : https://prove2.me/theorems/54ec6877-5f2e-4da0-b457-cfcd6373afec
-- title:
--   Theorem 5.5 (linear losses) — pseudo-regret of OSMD
-- statement:
--   Let $K$ be compact and convex, $F$ Legendre on $\bar D\supseteq K$ with $K\cap D\ne\emptyset$, and $\eta>0$. Let the losses be linear, $\ell_t(x)=\ell_t^\top x$, for fixed (oblivious) vectors $\ell_1,\ell_2,\dots$. OSMD plays a random point $\tilde x_t\in K$ and runs mirror descent with a random estimate $\tilde g_t$ satisfying $\mathbb E[\tilde g_t\mid x_t]=\ell_t$, and every dual step is well defined. Then for every norm $\|\cdot\|$ with dual norm $\|\cdot\|_*$ and every $x\in K$,
--   $$\mathbb E\sum_{t=1}^n\ell_t^\top\tilde x_t-\sum_{t=1}^n\ell_t^\top x\le\frac{\sup_{x\in K}F(x)-F(x_1)}{\eta}+\frac1\eta\sum_{t=1}^n\mathbb E\,D_{F^*}\bigl(\nabla F(x_t)-\eta\tilde g_t,\nabla F(x_t)\bigr)+\sum_{t=1}^n\mathbb E\bigl[\|x_t-\mathbb E[\tilde x_t\mid x_t]\|\,\|\tilde g_t\|_*\bigr].$$
--   The maximum of the left-hand side over $x\in K$ is the pseudo-regret $\bar R_n$.
--
--   When the perturbation is unbiased, $\mathbb E[\tilde x_t\mid x_t]=x_t$, the last sum vanishes. This gives the bound (5.6) on which the semi-bandit results (Theorems 5.6 and 5.7) and the Euclidean-ball result (Theorem 5.8) are built.
--
--   **Formalization Note** $\mathbb E[\cdot\mid x_t]$ is the coordinatewise conditional expectation given $\sigma(x_t)$. The iterates $x_t$ and the points $\tilde x_t$ are measurable, $x_1$ is the same on every sample path, and the coordinates of $\tilde g_t$ are integrable. The expectations on the right-hand side are assumed finite; otherwise the book's bound is trivial, while Lean's integral of a non-integrable function would be $0$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 75–76, Theorem 5.5 (second display, linear losses)

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_OMD

open MeasureTheory

namespace RegretBandits.Linear

/-- Theorem 5.5, linear losses (Pseudo-regret of OSMD; Bubeck, Cesa-Bianchi,
arXiv:1204.5721v2, pp. 75–76). OSMD on a compact convex `K ⊆ D̄` with Legendre `F`, `K ∩ D ≠ ∅`,
`η > 0`, linear losses `ℓ_t(x) = ℓ_tᵀx`, played points `x̃_t ∈ K` and estimates `g̃_t` with
`E[g̃_t | x_t] = ℓ_t`. Then for every norm `‖·‖` and every `x ∈ K`,
`E ∑ ℓ_tᵀx̃_t - ∑ ℓ_tᵀx ≤ (sup_K F - F(x_1))/η + (1/η) ∑ E D_{F*}(∇F(x_t) - η g̃_t, ∇F(x_t))
  + ∑ E[‖x_t - E[x̃_t | x_t]‖ ‖g̃_t‖_*]`. -/
theorem osmd_pseudo_regret_linear {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {F : (Fin d → ℝ) → ℝ} {D K : Set (Fin d → ℝ)}
    (hF : IsLegendre F D) (hKc : IsCompact K) (hKv : Convex ℝ K) (hKD : K ⊆ closure D)
    (hKne : (K ∩ D).Nonempty) {η : ℝ} (hη : 0 < η)
    (ℓ : ℕ → Fin d → ℝ)
    (x xt g w : ℕ → Ω → Fin d → ℝ) (x₁ : Fin d → ℝ)
    (hrun : ∀ ω, IsOMDRun F D K η (fun t => g t ω) (fun t => x t ω) (fun t => w t ω))
    (hx₁ : ∀ ω, x 1 ω = x₁)
    (hxm : ∀ t, 1 ≤ t → Measurable (x t)) (hxtm : ∀ t, 1 ≤ t → Measurable (xt t))
    (hxtK : ∀ t, 1 ≤ t → ∀ ω, xt t ω ∈ K)
    (hgi : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => g t ω i) P)
    (hunb : ∀ t, 1 ≤ t → condExpGiven P (x t) (g t) =ᵐ[P] fun _ => ℓ t)
    (hDi : ∀ t, 1 ≤ t →
      Integrable (fun ω => dualBregman F D (grad F (x t ω) - η • g t ω) (grad F (x t ω))) P)
    (N : (Fin d → ℝ) → ℝ) (hN : IsNorm N)
    (hNi : ∀ t, 1 ≤ t →
      Integrable (fun ω => N (x t ω - condExpGiven P (x t) (xt t) ω) * dualNorm N (g t ω)) P)
    (n : ℕ) :
    ∀ y ∈ K,
      ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ xt t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
        (sSup (F '' K) - F x₁) / η +
          (1 / η) * ∑ t ∈ Finset.Icc 1 n,
            ∫ ω, dualBregman F D (grad F (x t ω) - η • g t ω) (grad F (x t ω)) ∂P +
          ∑ t ∈ Finset.Icc 1 n,
            ∫ ω, N (x t ω - condExpGiven P (x t) (xt t) ω) * dualNorm N (g t ω) ∂P := by sorry

end RegretBandits.Linear
