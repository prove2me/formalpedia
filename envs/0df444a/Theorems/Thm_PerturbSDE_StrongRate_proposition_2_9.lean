-- Prove2me | Theorems.Thm_PerturbSDE_StrongRate_proposition_2_9
-- name    : PerturbSDE.StrongRate.proposition_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:09:00.875331+00:00
-- url     : https://prove2.me/theorems/0026f724-0e3a-469d-b0c3-4b7f5d1752bd
-- title:
--   Proposition 2.9, p. 11 — pathwise inequality (33) for ‖X−Y‖^p (finite-dimensional case H = ℝ^d, U = ℝ^m; restricted to ε ∈ (0, ∞))
-- statement:
--   Let $T\in(0,\infty)$, let $(\Omega,\mathcal F,\mathbb P,(\mathcal F_t))$ be a stochastic basis carrying a standard $m$-dimensional $(\mathcal F_t)$-Brownian motion $W$, let $\mathcal O\subseteq\mathbb R^d$ be a Borel set and let $\mu:\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times m}$ be measurable. Let $X,Y:[0,T]\times\Omega\to\mathcal O$ and predictable $a:[0,T]\times\Omega\to\mathbb R^d$, $b:[0,T]\times\Omega\to\mathbb R^{d\times m}$, $\chi:[0,T]\times\Omega\to\mathbb R$ satisfy
--   $$\int_0^T\|a_s\|+\|b_s\|^2_{HS}+|\chi_s|+\|\mu(X_s)\|+\|\sigma(X_s)\|^2_{HS}+\|\mu(Y_s)\|+\|\sigma(Y_s)\|^2_{HS}\,ds<\infty\quad\mathbb P\text{-a.s.},$$
--   $X_t=X_0+\int_0^t\mu(X_s)\,ds+\int_0^t\sigma(X_s)\,dW_s$ and $Y_t=Y_0+\int_0^ta_s\,ds+\int_0^tb_s\,dW_s$. Write $D_s=\exp(\int_0^s\chi_u\,du)$. Then $\mathbb P$-almost surely, for all $t\in[0,T]$, $\varepsilon\in(0,\infty)$ and $p\in[2,\infty)$,
--   $$\begin{aligned}\frac{\|X_t-Y_t\|^p}{D_t}\le{}&\|X_0-Y_0\|^p+\int_0^t\Big\langle\frac{p\|X_s-Y_s\|^{p-2}(X_s-Y_s)}{D_s},[\sigma(X_s)-b_s]\,dW_s\Big\rangle\\&+\int_0^t\frac{p\|X_s-Y_s\|^{p-2}\big[\langle X_s-Y_s,\mu(Y_s)-a_s\rangle+\frac{(p-1)(1+1/\varepsilon)}{2}\|b_s-\sigma(Y_s)\|^2_{HS}\big]-\chi_s\|X_s-Y_s\|^p}{D_s}\,ds\\&+\int_0^t\frac{p\|X_s-Y_s\|^{p-2}\big[\langle X_s-Y_s,\mu(X_s)-\mu(Y_s)\rangle+\frac{(p-1)(1+\varepsilon)}{2}\|\sigma(X_s)-\sigma(Y_s)\|^2_{HS}\big]}{D_s}\,ds,\end{aligned}$$
--   and both $ds$-integrands are integrable on $[0,t]$.
--
--   This is the pathwise Itô inequality for $V(x,y)=\|x-y\|^p$ from which the perturbation estimate, Theorem 2.10, is obtained by localization and Hölder's inequality.
--
--   **Formalization Note** The paper states the result for separable Hilbert spaces $H,U$ and $\varepsilon\in[0,\infty]$; this item is the finite-dimensional case $H=\mathbb R^d$, $U=\mathbb R^m$ and is **restricted to $\varepsilon\in(0,\infty)$** (at $\varepsilon\in\{0,\infty\}$ one integrand may be $+\infty$). The null set is uniform in $(t,\varepsilon,p)$, as in the paper's "a.s. for all $t,\varepsilon,p$". The stochastic integral is $\sum_j J^{(p)}_j(t)$, where $J^{(p)}_j$ is a continuous process pinned down by the published Brownian Itô-integral relation `EthierKurtz.HasBrownianItoIntegral` (completed filtration, integrand cut off after $T$); on the null set where $\int_0^T|\chi_s|\,ds=\infty$ the integrand is set to $0$, which does not change the Itô integral. The SDE solutions use the published `IsSolution` / `IsItoProcess` (continuous on $[0,T]$, adapted to the completed filtration, normal filtration = right-continuity + completion, $W$ on $[0,\infty)$); the paper's predictability of $X,Y$ is then automatic, and $a,b,\chi$ are predictable with respect to $(\mathcal F_t)$. Powers are real powers with $0^0=1$.
-- source:
--   Hutzenthaler, Jentzen, arXiv:1401.0295v1, p. 11, Proposition 2.9, (33)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_completedSDEPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_PerturbSDE_StrongRate_Setting
import Definitions.Def_PerturbSDE_StrongRate_Perturbation

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PerturbSDE.StrongRate

open EthierKurtz SabanisEuler.Shared

/-- Hutzenthaler–Jentzen, arXiv:1401.0295v1, p. 11, Proposition 2.9, (33), finite-dimensional
case `H = ℝ^d`, `U = ℝ^m`, restricted to `ε ∈ (0, ∞)`. Almost surely, simultaneously for all
`p ∈ [2, ∞)`, `t ∈ [0, T]` and `ε ∈ (0, ∞)`,
`‖X_t − Y_t‖^p / e^{∫_0^t χ} ≤ ‖X_0 − Y_0‖^p + ∫_0^t ⟨G^{(p)}_s, [σ(X_s) − b_s] dW_s⟩
   + ∫_0^t [p ‖X_s − Y_s‖^{p−2} [⟨X_s − Y_s, µ(Y_s) − a_s⟩ + ((p−1)(1+1/ε)/2) ‖b_s − σ(Y_s)‖²]
           − χ_s ‖X_s − Y_s‖^p] / e^{∫_0^s χ} ds
   + ∫_0^t p ‖X_s − Y_s‖^{p−2} [⟨X_s − Y_s, µ(X_s) − µ(Y_s)⟩ + ((p−1)(1+ε)/2) ‖σ(X_s) − σ(Y_s)‖²]
           / e^{∫_0^s χ} ds`,
where `G^{(p)}_s = p ‖X_s − Y_s‖^{p−2} (X_s − Y_s) / e^{∫_0^s χ}`. The stochastic integral is
`∑_j J p j t`, where `J p j` is the continuous Brownian Itô integral (published relation
`EthierKurtz.HasBrownianItoIntegral`) of the scalar integrand `⟨G^{(p)}_s, σ_j(X_s) − b_s e_j⟩`
against `W^{(j)}`; on the `P`-null set where `∫_0^T |χ_s| ds = ∞` the integrand is set to `0`.
Both `ds`-integrands are asserted to be integrable on `[0, t]`. -/
theorem proposition_2_9 {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) {Ω : Type*}
    [mΩ : MeasurableSpace Ω]
    (T : ℝ≥0) (hT : 0 < T) (𝒪 : Set (SDEState d)) (h𝒪 : MeasurableSet 𝒪)
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState m) (hW : IsWienerMartingale P ℱ W)
    (mu : SDEState d → SDEState d) (sigma : SDEState d → Diffusion d m)
    (hmu : Measurable mu) (hsigma : Measurable sigma)
    (X Y : ℝ≥0 → Ω → SDEState d) (hX𝒪 : ∀ t ≤ T, ∀ ω, X t ω ∈ 𝒪)
    (hY𝒪 : ∀ t ≤ T, ∀ ω, Y t ω ∈ 𝒪)
    (a : ℝ≥0 → Ω → SDEState d) (b : ℝ≥0 → Ω → Diffusion d m) (χ : ℝ≥0 → Ω → ℝ)
    (ha : IsStronglyPredictable ℱ a) (hb : IsStronglyPredictable ℱ b)
    (hχ : IsStronglyPredictable ℱ χ)
    (hint : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a s.toNNReal ω‖ₑ + ‖b s.toNNReal ω‖ₑ ^ 2 + ‖χ s.toNNReal ω‖ₑ +
        ‖mu (X s.toNNReal ω)‖ₑ + ‖sigma (X s.toNNReal ω)‖ₑ ^ 2 + ‖mu (Y s.toNNReal ω)‖ₑ +
        ‖sigma (Y s.toNNReal ω)‖ₑ ^ 2) < ⊤)
    (hX : IsSolution P ℱ W T (X 0) (fun z => mu z.2) (fun z => sigma z.2) X)
    (hY : IsItoProcess P ℱ W T (Y 0) a b Y) :
    ∃ J : ℝ → Fin m → ℝ≥0 → Ω → ℝ,
      (∀ p j ω, Continuous (fun t => J p j t ω)) ∧
      (∀ p : ℝ, 2 ≤ p → ∀ j : Fin m,
        HasBrownianItoIntegral P (completedSDEPast P ℱ) (fun t ω => W t ω j)
          (fun t ω => if t ≤ T ∧ ∫⁻ u in Set.Icc (0 : ℝ) T, ‖χ u.toNNReal ω‖ₑ < ⊤ then
              inner ℝ ((p * ‖X t ω - Y t ω‖ ^ (p - 2) / discount χ t ω) • (X t ω - Y t ω))
                (col (sigma (X t ω)) j - col (b t ω) j)
            else 0)
          (J p j)) ∧
      ∀ᵐ ω ∂P, ∀ p : ℝ, 2 ≤ p → ∀ t ≤ T, ∀ ε : ℝ, 0 < ε →
        IntervalIntegrable (fun s : ℝ =>
            (p * ‖X s.toNNReal ω - Y s.toNNReal ω‖ ^ (p - 2) *
                (inner ℝ (X s.toNNReal ω - Y s.toNNReal ω) (mu (Y s.toNNReal ω) - a s.toNNReal ω) +
                  (p - 1) * (1 + 1 / ε) / 2 * ‖b s.toNNReal ω - sigma (Y s.toNNReal ω)‖ ^ 2) -
              χ s.toNNReal ω * ‖X s.toNNReal ω - Y s.toNNReal ω‖ ^ p) /
            discount χ s.toNNReal ω) volume 0 (t : ℝ) ∧
        IntervalIntegrable (fun s : ℝ =>
            p * ‖X s.toNNReal ω - Y s.toNNReal ω‖ ^ (p - 2) *
                (inner ℝ (X s.toNNReal ω - Y s.toNNReal ω)
                    (mu (X s.toNNReal ω) - mu (Y s.toNNReal ω)) +
                  (p - 1) * (1 + ε) / 2 * ‖sigma (X s.toNNReal ω) - sigma (Y s.toNNReal ω)‖ ^ 2) /
            discount χ s.toNNReal ω) volume 0 (t : ℝ) ∧
        ‖X t ω - Y t ω‖ ^ p / discount χ t ω ≤
          ‖X 0 ω - Y 0 ω‖ ^ p + ∑ j, J p j t ω +
            (∫ s in (0 : ℝ)..(t : ℝ),
              (p * ‖X s.toNNReal ω - Y s.toNNReal ω‖ ^ (p - 2) *
                  (inner ℝ (X s.toNNReal ω - Y s.toNNReal ω)
                      (mu (Y s.toNNReal ω) - a s.toNNReal ω) +
                    (p - 1) * (1 + 1 / ε) / 2 * ‖b s.toNNReal ω - sigma (Y s.toNNReal ω)‖ ^ 2) -
                χ s.toNNReal ω * ‖X s.toNNReal ω - Y s.toNNReal ω‖ ^ p) /
              discount χ s.toNNReal ω) +
            ∫ s in (0 : ℝ)..(t : ℝ),
              p * ‖X s.toNNReal ω - Y s.toNNReal ω‖ ^ (p - 2) *
                  (inner ℝ (X s.toNNReal ω - Y s.toNNReal ω)
                      (mu (X s.toNNReal ω) - mu (Y s.toNNReal ω)) +
                    (p - 1) * (1 + ε) / 2 *
                      ‖sigma (X s.toNNReal ω) - sigma (Y s.toNNReal ω)‖ ^ 2) /
              discount χ s.toNNReal ω := by sorry

end PerturbSDE.StrongRate
