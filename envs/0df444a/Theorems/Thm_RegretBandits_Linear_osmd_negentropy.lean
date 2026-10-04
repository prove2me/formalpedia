-- Prove2me | Theorems.Thm_RegretBandits_Linear_osmd_negentropy
-- name    : RegretBandits.Linear.osmd_negentropy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:33:55.218762+00:00
-- url     : https://prove2.me/theorems/7e799a09-5f3b-476e-a4ae-d2dcf9990423
-- title:
--   Theorem 5.6 — OSMD with negative entropy: $\bar R_n\le\sqrt{2mdn\ln(d/m)}$
-- statement:
--   Consider online combinatorial optimization with semi-bandit feedback. The arm set is a nonempty $\mathcal C\subseteq\{0,1\}^d$ with $\|v\|_1=m$ for all $v\in\mathcal C$, the convex hull $\mathcal K=\mathrm{Conv}(\mathcal C)$ meets $(0,+\infty)^d$, and the losses $\ell_t\in[0,1]^d$ are fixed in advance. Run OSMD on $\mathcal K$ with the negative entropy $F(x)=\sum_i x_i\ln x_i-\sum_i x_i$, playing random arms $v_t\in\mathcal C$ with $\mathbb E[v_t\mid x_t]=x_t$.
--
--   1. If the loss estimates $\tilde\ell_t$ are non-negative and unbiased, $\mathbb E[\tilde\ell_t\mid x_t]=\ell_t$, then for every $\eta>0$ and every $x\in\mathcal K$
--   $$\mathbb E\sum_{t=1}^n\ell_t^\top v_t-\sum_{t=1}^n\ell_t^\top x\ \le\ \frac m\eta\ln\frac dm+\frac\eta2\sum_{t=1}^n\sum_{i=1}^d\mathbb E\bigl[x_t(i)\,\tilde\ell_t(i)^2\bigr].$$
--   2. With the estimate (5.5) and $\eta=\sqrt{\frac{2m}{nd}\ln\frac dm}$,
--   $$\mathbb E\sum_{t=1}^n\ell_t^\top v_t-\sum_{t=1}^n\ell_t^\top x\ \le\ \sqrt{2mdn\ln\frac dm}.$$
--
--   The maximum of the left-hand side over $x\in\mathcal K$ is the pseudo-regret $\bar R_n$. For $\mathcal C=\{e_1,\dots,e_d\}$ this recovers the $\sqrt{2dn\ln d}$ bound of Exp3. Theorem 5.7 removes the logarithmic factor.
--
--   **Formalization Note** The book's statement says "loss estimates $\tilde\ell_t$". Non-negativity is used in its proof ("since $\tilde\ell_t(i)\ge0$") and unbiasedness in the step (5.6) the proof starts from, so both are stated as hypotheses of part 1. $\mathcal K\cap(0,+\infty)^d\neq\emptyset$ is the OMD requirement $K\cap D\ne\emptyset$ (p. 71), i.e. every coordinate is used by some arm. Part 1 assumes measurable iterates and arms, integrable estimates, and finite expectations on the right-hand side; part 2 assumes measurable iterates and arms. $\mathbb E[\cdot\mid x_t]$ is conditioning on $\sigma(x_t)$, and $0\ln0=0$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 78, Theorem 5.6 (setting on p. 77, Eq. (5.5))

import Mathlib
import Definitions.Def_RegretBandits_Linear_ConvexBasics
import Definitions.Def_RegretBandits_Linear_OMD
import Definitions.Def_RegretBandits_Linear_Potential
import Definitions.Def_RegretBandits_Linear_SemiBandit

open MeasureTheory

namespace RegretBandits.Linear

/-- Theorem 5.6 (OSMD with negative entropy; Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 78).
Semi-bandit setting of p. 77: arms `C ⊆ {0,1}^d` with `‖v‖₁ = m`, `K = Conv(C)`, oblivious losses
`ℓ_t ∈ [0,1]^d`. OSMD on `K` with `F(x) = ∑ x_i ln x_i - ∑ x_i`, played arms `v_t ∈ C` with
`E[v_t | x_t] = x_t`, and non-negative estimates `ℓ̃_t` with `E[ℓ̃_t | x_t] = ℓ_t`, satisfies, for
every `x ∈ K`,
`E ∑ ℓ_tᵀv_t - ∑ ℓ_tᵀx ≤ (m/η) ln(d/m) + (η/2) ∑_t ∑_i E[x_t(i) ℓ̃_t(i)²]`.
With the estimate (5.5) and `η = √((2m/(nd)) ln(d/m))` it satisfies
`E ∑ ℓ_tᵀv_t - ∑ ℓ_tᵀx ≤ √(2mdn ln(d/m))`. -/
theorem osmd_negentropy {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Set (Fin d → ℝ)} (hC : IsCombinatorialSet C m)
    (hKD : (convexHull ℝ C ∩ posOrthant d).Nonempty)
    (ℓ : ℕ → Fin d → ℝ) (hℓ : ∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    (∀ (η : ℝ), 0 < η → ∀ (x v ℓt w : ℕ → Ω → Fin d → ℝ),
      (∀ ω, IsOMDRun negEntropy (posOrthant d) (convexHull ℝ C) η
        (fun t => ℓt t ω) (fun t => x t ω) (fun t => w t ω)) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      (∀ t, 1 ≤ t → ∀ ω i, 0 ≤ ℓt t ω i) →
      (∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => ℓt t ω i) P) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (ℓt t) =ᵐ[P] fun _ => ℓ t) →
      (∀ t, 1 ≤ t → ∀ i, Integrable (fun ω => x t ω i * ℓt t ω i ^ 2) P) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          (m : ℝ) / η * Real.log ((d : ℝ) / m) +
            η / 2 * ∑ t ∈ Finset.Icc 1 n, ∑ i, ∫ ω, x t ω i * ℓt t ω i ^ 2 ∂P) ∧
    (∀ (x v w : ℕ → Ω → Fin d → ℝ),
      (∀ ω, IsOMDRun negEntropy (posOrthant d) (convexHull ℝ C)
        (Real.sqrt (2 * m / (n * d) * Real.log ((d : ℝ) / m)))
        (fun t => semiBanditEstimate (ℓ t) (v t ω) (x t ω)) (fun t => x t ω)
        (fun t => w t ω)) →
      (∀ t, 1 ≤ t → Measurable (x t)) → (∀ t, 1 ≤ t → Measurable (v t)) →
      (∀ t, 1 ≤ t → ∀ ω, v t ω ∈ C) →
      (∀ t, 1 ≤ t → condExpGiven P (x t) (v t) =ᵐ[P] x t) →
      ∀ y ∈ convexHull ℝ C,
        ∫ ω, ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ v t ω ∂P - ∑ t ∈ Finset.Icc 1 n, ℓ t ⬝ᵥ y ≤
          Real.sqrt (2 * m * d * n * Real.log ((d : ℝ) / m))) := by sorry

end RegretBandits.Linear
