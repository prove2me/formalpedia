-- Prove2me | Theorems.Thm_StochApproxDyn_SubgaussianNoise_directional_maximal_tail
-- name    : StochApproxDyn.SubgaussianNoise.directional_maximal_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:09:43.036167+00:00
-- url     : https://prove2.me/theorems/94df008f-5edb-4cbd-9b5f-43f4789f45a7
-- title:
--   Maximal tail bound for the weighted noise sums in a fixed direction
-- statement:
--   Let $\{x_n\}$ be a Robbins–Monro algorithm $x_{n+1}-x_n=\gamma_{n+1}(F(x_n)+U_{n+1})$ whose noise $\{U_n\}$ is subgaussian with constant $\Gamma>0$. Let $\tau_n=\sum_{i=1}^n\gamma_i$ and $m(t)=\sup\{k\ge0:\tau_k\le t\}$. Fix a unit vector $e\in\mathbb R^d$, $\alpha>0$, $n\in\mathbb N$ and $T>0$, and write $N=m(\tau_n+T)$. Then
--   $$P\Big(\sup_{n<k\le N}\Big\langle e,\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}\Big\rangle\ge\alpha\Big)\le\exp\Big(\frac{-\alpha^2}{2\Gamma\sum_{i=n}^{N-1}\gamma_{i+1}^2}\Big).$$
--
--   The paper uses this bound for the $2d$ directions $e\in\{\pm e_1,\dots,\pm e_d\}$ of the canonical basis; combining them controls the norm of the noise sums over a time window of length $T$, which leads to estimate (18).
--
--   **Formalization Note** The event "the supremum over the finite range $n<k\le N$ is at least $\alpha$" is written as "some $k$ in that range has $\langle e,\cdot\rangle\ge\alpha$"; an empty range gives the empty event. The statement is for every unit vector $e$, which contains the paper's case. If $\sum_{i=n}^{N-1}\gamma_{i+1}^2=0$ the intended right side is $e^{-\infty}=0$, but Lean's division by $0$ gives $e^{0}=1$; the statement is then trivially true, and also true in the intended reading since every noise sum in the range vanishes.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.2, proof of Proposition 4.4, p. 17 (PDF p. 18), unnumbered displays after 'Set R = α/(Γ Σ γ²_{i+1}), β = Rα and θ = Re'

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.SubgaussianNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.4, p. 17: maximal tail bound in a fixed direction.
For a Robbins–Monro algorithm with subgaussian noise (constant `Γ`), every unit vector `e`,
every `α > 0`, every `n` and every `T > 0`,
`P(sup_{n < k ≤ m(τ_n+T)} ⟨e, ∑_{i=n}^{k-1} γ_{i+1} U_{i+1}⟩ ≥ α)
  ≤ exp(−α² / (2Γ ∑_{i=n}^{m(τ_n+T)-1} γ_{i+1}²))`.
The supremum over the finite range of `k` is at least `α` iff some term is; the event is
written that way (an empty range gives the empty event). When the block sum of `γ²` vanishes,
Lean's `x / 0 = 0` makes the right side `1`, so the bound is then trivially true (and the left
side is `0` anyway). The paper states it for `e ∈ {±e_1, …, ±e_d}`; every unit vector is
allowed here. -/
theorem directional_maximal_tail {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (Γ : ℝ) (hΓ : 0 < Γ) (hsg : IsSubgaussianWith P ℱ U Γ)
    (e : EuclideanSpace ℝ (Fin d)) (he : ‖e‖ = 1) (α : ℝ) (hα : 0 < α)
    (n : ℕ) (T : ℝ) (hT : 0 < T) :
    P {ω | ∃ k ∈ Finset.Ioc n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
        α ≤ ⟪e, ∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω⟫_ℝ}
      ≤ ENNReal.ofReal (Real.exp (-α ^ 2 /
          (2 * Γ * ∑ i ∈ Finset.Ico n (StochApproxDyn.MartingaleNoise.stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)), γ (i + 1) ^ 2))) := by sorry

end StochApproxDyn.SubgaussianNoise
