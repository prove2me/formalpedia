-- Prove2me | Theorems.Thm_RegretBandits_Linear_osmd_zero_potential
-- name    : RegretBandits.Linear.osmd_zero_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:33:50.22538+00:00
-- url     : https://prove2.me/theorems/22e7826c-295c-4763-863e-0741bdcf8373
-- title:
--   Theorem 5.7 — OSMD with a 0-potential: $\bar R_n\le q\sqrt{2mdn/(q-1)}$ for semi-bandits
-- statement:
--   Consider online combinatorial optimization with semi-bandit feedback. The arm set is a nonempty $\mathcal C\subseteq\{0,1\}^d$ with $\|v\|_1=m$ for all $v\in\mathcal C$, the convex hull $\mathcal K=\mathrm{Conv}(\mathcal C)$ meets $(0,+\infty)^d$, and the losses $\ell_t\in[0,1]^d$ are fixed in advance. OSMD on $\mathcal K$ plays random arms $v_t\in\mathcal C$ with $\mathbb E[v_t\mid x_t]=x_t$.
--
--   1. Let $\psi$ be a $0$-potential and run OSMD with $F_\psi$ and non-negative, unbiased loss estimates $\tilde\ell_t$ ($\mathbb E[\tilde\ell_t\mid x_t]=\ell_t$). Then for every $\eta>0$ and every $x\in\mathcal K$
--   $$\mathbb E\sum_{t=1}^n\ell_t^\top v_t-\sum_{t=1}^n\ell_t^\top x\ \le\ \frac{\sup_{x\in\mathcal K}F_\psi(x)-F_\psi(x_1)}{\eta}+\frac\eta2\sum_{t=1}^n\sum_{i=1}^d\mathbb E\left[\frac{\tilde\ell_t(i)^2}{(\psi^{-1})'(x_t(i))}\right].$$
--   2. Let $q>1$, $\psi(x)=(-x)^{-q}$, the estimate (5.5), and
--   $$\eta=\sqrt{\frac{2}{q-1}\cdot\frac{m^{1-2/q}}{n\,d^{1-2/q}}}.$$
--   Then
--   $$\mathbb E\sum_{t=1}^n\ell_t^\top v_t-\sum_{t=1}^n\ell_t^\top x\ \le\ q\sqrt{\frac{2}{q-1}\,mdn}.$$
--   3. With $q=2$, i.e. $\eta=\sqrt{2/n}$, this is $2\sqrt{2mdn}$.
--
--   The maximum of the left-hand side over $x\in\mathcal K$ is the pseudo-regret $\bar R_n$. The bound improves Theorem 5.6 by the factor $\sqrt{\ln(d/m)}$. For $m=1$ it is the log-free $O(\sqrt{dn})$ bound for the adversarial multi-armed bandit.
--
--   **Formalization Note** *Corrected misprint:* the book prints $\eta=\sqrt{\frac2{q-1}\frac{m^{1-2/q}}{d^{1-2/q}}}$, without the factor $1/n$. The proof bounds $\sup F_\psi-F_\psi(x_1)$ by $\frac q{q-1}m^{(q-1)/q}d^{1/q}$ and the second term by $q\,m^{1/q}d^{1-1/q}$ per round (p. 81). The stated bound $q\sqrt{2mdn/(q-1)}$ is attained by the $\eta$ above, which includes $n$. $q>1$ is needed for $\psi$ to be a $0$-potential. Non-negativity of the estimates is in the book's statement. Unbiasedness is the standing assumption of Section 5.4 behind (5.6). $\mathcal K\cap(0,+\infty)^d\ne\emptyset$ is the OMD requirement $K\cap D\ne\emptyset$. $x_1$ is the same on every sample path. Iterates and arms are measurable; in part 1 the estimates and the right-hand side expectations are assumed integrable. $\mathbb E[\cdot\mid x_t]$ is conditioning on $\sigma(x_t)$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 80, Theorem 5.7 (setting on p. 77, Eq. (5.5); proof on p. 81)

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_OMD
import Definitions.Def_RegretBandits_Linear_Potential
import Definitions.Def_RegretBandits_Linear_SemiBandit

open MeasureTheory

namespace RegretBandits.Linear

/-- Theorem 5.7 (OSMD with a 0-potential; Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 80).
Semi-bandit setting of p. 77: arms `C ⊆ {0,1}^d` with `‖v‖₁ = m`, `K = Conv(C)`, oblivious losses
`ℓ_t ∈ [0,1]^d`, played arms `v_t ∈ C` with `E[v_t | x_t] = x_t`.
1. For every `0`-potential `ψ`, OSMD on `K` with `F_ψ` and non-negative estimates `ℓ̃_t` with
   `E[ℓ̃_t | x_t] = ℓ_t` satisfies, for every `x ∈ K`,
   `E ∑ ℓ_tᵀv_t - ∑ ℓ_tᵀx ≤ (sup_K F_ψ - F_ψ(x_1))/η + (η/2) ∑_t ∑_i E[ℓ̃_t(i)² / (ψ⁻¹)'(x_t(i))]`.
2. For `q > 1`, `ψ(x) = (-x)^{-q}`, the estimate (5.5) and
   `η = √((2/(q-1)) m^{1-2/q} / (n d^{1-2/q}))` (corrected: the book prints no `n`),
   `E ∑ ℓ_tᵀv_t - ∑ ℓ_tᵀx ≤ q √((2/(q-1)) m d n)`.
3. With `q = 2` (`η = √(2/n)`): `E ∑ ℓ_tᵀv_t - ∑ ℓ_tᵀx ≤ 2 √(2mdn)`. -/
theorem osmd_zero_potential {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Set (Fin d → ℝ)} (hC : IsCombinatorialSet C m)
    (hKD : (convexHull ℝ C ∩ posOrthant d).Nonempty)
    (ℓ : ℕ → Fin d → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (∀ (ψ : ℝ → ℝ) (a : EReal), IsPotential 0 a ψ →
      ∀ (η : ℝ), 0 < η → ∀ (x v ℓt w : ℕ → Ω → Fin d → ℝ) (x₁ : Fin d → ℝ),
      (∀ ω, IsOMDRun (potentialFn ψ a 0) (posOrthant d) (convexHull ℝ C) η
        (fun t => ℓt t ω) (fun t => x t ω) (fun t => w t ω)) →
      (∀ ω, x 1 ω = x₁) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      (∀ t, 1 ≤ t → ∀ ω i, 0 ≤ ℓt t ω i) →
      (∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => ℓt t ω i) P) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (ℓt t) =ᵐ[P] fun _ => ℓ t) →
      (∀ t, 1 ≤ t → ∀ i,
        Integrable (fun ω => ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i)) P) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          (sSup (potentialFn ψ a 0 '' convexHull ℝ C) - potentialFn ψ a 0 x₁) / η +
            η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i,
              ∫ ω, ℓt t ω i ^ 2 / deriv (potInv ψ a) (x t ω i) ∂P) ∧
    (∀ (q : ℝ), 1 < q → ∀ (x v w : ℕ → Ω → Fin d → ℝ),
      (∀ ω, IsOMDRun (potentialFn (powPotential q) 0 0) (posOrthant d) (convexHull ℝ C)
        (Real.sqrt (2 / (q - 1) * (m : ℝ) ^ (1 - 2 / q) / (n * (d : ℝ) ^ (1 - 2 / q))))
        (fun t => semiBanditEstimate (ℓ t) (v t ω) (x t ω)) (fun t => x t ω)
        (fun t => w t ω)) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          q * Real.sqrt (2 / (q - 1) * m * d * n)) ∧
    (∀ (x v w : ℕ → Ω → Fin d → ℝ),
      (∀ ω, IsOMDRun (potentialFn (powPotential 2) 0 0) (posOrthant d) (convexHull ℝ C)
        (Real.sqrt (2 / n))
        (fun t => semiBanditEstimate (ℓ t) (v t ω) (x t ω)) (fun t => x t ω)
        (fun t => w t ω)) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          2 * Real.sqrt (2 * m * d * n)) := by sorry

end RegretBandits.Linear
