-- Prove2me | Theorems.Thm_RegretBandits_Linear_osmd_pseudo_regret
-- name    : RegretBandits.Linear.osmd_pseudo_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:33:08.153346+00:00
-- url     : https://prove2.me/theorems/c09ec936-7246-4204-b1a3-7d8de23d89b3
-- title:
--   Theorem 5.5 (first bound, corrected) — pseudo-regret of OSMD for subdifferentiable losses
-- statement:
--   Let $K$ be compact and convex, $F$ Legendre on $\bar D\supseteq K$ with $K\cap D\ne\emptyset$, and $\eta>0$. Let $\ell_1,\ell_2,\dots$ be fixed (oblivious) losses on $K$ with subgradients $\nabla\ell_t(z)$ at every $z\in K$. OSMD plays a random point $\tilde x_t\in K$ and runs mirror descent with a random estimate $\tilde g_t$ satisfying
--   $$\mathbb E[\tilde g_t\mid x_t]=\nabla\ell_t(x_t),$$
--   and every dual step is well defined. Then for every norm $\|\cdot\|$ with dual norm $\|\cdot\|_*$ and every $x\in K$,
--   $$\mathbb E\sum_{t=1}^n\ell_t(\tilde x_t)-\sum_{t=1}^n\ell_t(x)\le\frac{\sup_{x\in K}F(x)-F(x_1)}{\eta}+\frac1\eta\sum_{t=1}^n\mathbb E\,D_{F^*}\bigl(\nabla F(x_t)-\eta\tilde g_t,\nabla F(x_t)\bigr)+\sum_{t=1}^n\mathbb E\bigl[\|x_t-\tilde x_t\|\,\|\nabla\ell_t(\tilde x_t)\|_*\bigr].$$
--   Since the losses are fixed, the maximum of the left-hand side over $x\in K$ is the pseudo-regret $\bar R_n=\mathbb E\sum_t\ell_t(\tilde x_t)-\min_{x\in K}\mathbb E\sum_t\ell_t(x)$.
--
--   The bound reduces the bandit problem to the design of an unbiased gradient estimate with a small dual-divergence term. It is the template for the bandit convex optimization results of Chapter 6.
--
--   **Formalization Note** *Corrected misprint:* the book prints $\|\tilde g_t\|_*$ in the last term. With that term the statement is false. Take $d=1$, $K=[-1,1]$, $F(x)=x^2/2$, $\ell_t(x)=x^2$, $\tilde g_t=\nabla\ell_t(x_t)=0$, and $\tilde x_t=\pm1$ with probability $1/2$ each. Then $x_t=0$ for all $t$, the pseudo-regret is $n$, and the printed right-hand side is $1/(2\eta)$. The proof's step $\ell_t(\tilde x_t)-\ell_t(x_t)\le\|x_t-\tilde x_t\|\,\|\cdot\|_*$ holds with a subgradient at $\tilde x_t$, which is the term stated here. The linear-loss bound of the theorem is a separate item. Standing conventions: the subgradient selection $\nabla\ell_t$ is an explicit input; the iterates $x_t$ and the points $\tilde x_t$ are measurable; $x_1$ is the same on every sample path; $\mathbb E[\cdot\mid x_t]$ is conditioning on $\sigma(x_t)$. Every expectation on the right-hand side is assumed finite (otherwise the book's bound is trivial, while Lean's integral of a non-integrable function would be $0$).
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 75–76, Theorem 5.5 (first display; pseudo-regret defined on p. 75)

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_OMD

open MeasureTheory

namespace RegretBandits.Linear

/-- Theorem 5.5, first bound, corrected (Pseudo-regret of OSMD; Bubeck, Cesa-Bianchi,
arXiv:1204.5721v2, pp. 75–76). OSMD on a compact convex `K ⊆ D̄` with Legendre `F`, `K ∩ D ≠ ∅`,
`η > 0`, losses `ℓ_t` on `K` with subgradients `G_t(z)` at every `z ∈ K`, played points
`x̃_t ∈ K`, and estimates `g̃_t` with `E[g̃_t | x_t] = ∇ℓ_t(x_t) = G_t(x_t)`. Then for every norm
`‖·‖` and every `x ∈ K`,
`E ∑ ℓ_t(x̃_t) - ∑ ℓ_t(x) ≤ (sup_K F - F(x_1))/η + (1/η) ∑ E D_{F*}(∇F(x_t) - η g̃_t, ∇F(x_t))
  + ∑ E[‖x_t - x̃_t‖ ‖∇ℓ_t(x̃_t)‖_*]`.
The book prints `‖g̃_t‖_*` in the last term; that version is false (see the Formalization Note
of the item), and the proof's step `ℓ_t(x̃_t) - ℓ_t(x_t) ≤ ‖x_t - x̃_t‖ ‖·‖_*` holds with the
subgradient at `x̃_t`. Losses are oblivious, so `min_{x ∈ K} E ∑ ℓ_t(x)` is `min_{x∈K} ∑ ℓ_t(x)`,
and the bound is stated for every comparator `x ∈ K`. -/
theorem osmd_pseudo_regret {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {F : (Fin d → ℝ) → ℝ} {D K : Set (Fin d → ℝ)}
    (hF : IsLegendre F D) (hKc : IsCompact K) (hKv : Convex ℝ K) (hKD : K ⊆ closure D)
    (hKne : (K ∩ D).Nonempty) {η : ℝ} (hη : 0 < η)
    (ℓ : ℕ → (Fin d → ℝ) → ℝ) (G : ℕ → (Fin d → ℝ) → Fin d → ℝ)
    (hG : ∀ t, 1 ≤ t → ∀ z ∈ K, ∀ y ∈ K, ℓ t z - ℓ t y ≤ G t z ⬝ᵥ (z - y))
    (x xt g w : ℕ → Ω → Fin d → ℝ) (x₁ : Fin d → ℝ)
    (hrun : ∀ ω, IsOMDRun F D K η (fun t => g t ω) (fun t => x t ω) (fun t => w t ω))
    (hx₁ : ∀ ω, x 1 ω = x₁)
    (hxm : ∀ t, 1 ≤ t → Measurable (x t)) (hxtm : ∀ t, 1 ≤ t → Measurable (xt t))
    (hxtK : ∀ t, 1 ≤ t → ∀ ω, xt t ω ∈ K)
    (hgi : ∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => g t ω i) P)
    (hunb : ∀ t, 1 ≤ t → condExpGiven P (x t) (g t) =ᵐ[P] fun ω => G t (x t ω))
    (hℓi : ∀ t, 1 ≤ t → Integrable (fun ω => ℓ t (xt t ω)) P)
    (hDi : ∀ t, 1 ≤ t →
      Integrable (fun ω => dualBregman F D (grad F (x t ω) - η • g t ω) (grad F (x t ω))) P)
    (N : (Fin d → ℝ) → ℝ) (hN : IsNorm N)
    (hNi : ∀ t, 1 ≤ t →
      Integrable (fun ω => N (x t ω - xt t ω) * dualNorm N (G t (xt t ω))) P)
    (n : ℕ) :
    ∀ y ∈ K,
      ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t (xt t ω) ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t y ≤
        (sSup (F '' K) - F x₁) / η +
          (1 / η) * ∑ t ∈ Finset.Icc 1 n,
            ∫ ω, dualBregman F D (grad F (x t ω) - η • g t ω) (grad F (x t ω)) ∂P +
          ∑ t ∈ Finset.Icc 1 n, ∫ ω, N (x t ω - xt t ω) * dualNorm N (G t (xt t ω)) ∂P := by sorry

end RegretBandits.Linear
