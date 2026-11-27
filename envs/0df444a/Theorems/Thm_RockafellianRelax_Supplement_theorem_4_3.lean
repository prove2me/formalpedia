-- Prove2me | Theorems.Thm_RockafellianRelax_Supplement_theorem_4_3
-- name    : RockafellianRelax.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:17:07.418353+00:00
-- url     : https://prove2.me/theorems/62246ea2-7168-5527-b171-f09a0d3c2287
-- title:
--   Theorem 4.3 — rates in expectation minimization (corrected: $3\beta^2/(2\alpha)$ replaces $\sqrt{3/(2\alpha)}\,\beta$ in $\sigma$)
-- statement:
--   Let $f_i : \mathbb R^n\to\overline{\mathbb R}$, $i = 0,1,\dots,s$, be proper and lower semicontinuous, let $p \in \Delta = \{q\in[0,\infty)^s \mid \sum_i q_i = 1\}$, and let $\varphi = f_0 + \sum_{i=1}^s p_i f_i$ be the objective of the actual problem (2.1), with $0\cdot\infty = 0$. Let $\rho \ge 0$. For $p^\nu \in \Delta$ and $\theta^\nu \ge 0$ let
--
--   $$
--   f^\nu(u,x) = f_0(x) + \sum_{i=1}^s (p^\nu_i+u_i) f_i(x) + \tfrac12\theta^\nu\|u\|_2^2
--   $$
--
--   if $p^\nu + u\in\Delta$, and $+\infty$ otherwise, as in (4.3). Consider $\varepsilon\in[0,2\rho]$ and sequences $p^\nu,\theta^\nu,y^\nu,(u^\nu,x^\nu)$ with these properties:
--
--   - the actual problem has a minimizer in $\mathbb B(0,\rho)$, and each problem (4.4) of minimizing $f^\nu(u,x) - \langle y^\nu,u\rangle$ has a minimizer in $\mathbb B(0,\rho)\times\mathbb B(0,\rho)$ (Euclidean balls);
--   - all these minimum values lie in $[-\rho,\rho-\varepsilon]$;
--   - $(u^\nu,x^\nu)\in\varepsilon\text{-}\operatorname{argmin}_{u,x} f^\nu(u,x)-\langle y^\nu,u\rangle$, with $\|u^\nu\|_2\le\rho$ and $\|x^\nu\|_2\le\rho$;
--   - $\{y^\nu\}$ is bounded.
--
--   For constants $\sigma,\tau$ write $\eta^\nu = \sigma\|p^\nu-p\|_2 + \max\{\tfrac12\theta^\nu\|p^\nu-p\|_2^2,\ \tau/\sqrt{\theta^\nu}\}$, and consider the error bound
--
--   $$
--   \operatorname{dist}\bigl(x^\nu,\ (\varepsilon+2\eta^\nu)\text{-}\operatorname{argmin}\varphi\bigr)\le\eta^\nu, \tag{4.5}
--   $$
--
--   where the distance is Euclidean and is $+\infty$ to the empty set.
--
--   1. **Existence.** For every $Y\in\mathbb R$ there are $\sigma>0$, $\tau>0$, $\Theta>0$ and $\delta>0$, depending only on $n$, $s$, $p$, the $f_i$, $\rho$ and $Y$, such that for all $\varepsilon$ and all such sequences with $\|y^\nu\|_2\le Y$ for every $\nu$, (4.5) holds at each $\nu$ with $\theta^\nu\ge\Theta$ and $\|p^\nu-p\|_2\le\delta$.
--   2. **Explicit constants.** For all such $\varepsilon$ and sequences, let $\kappa\ge0$ satisfy $f_0(x)\ge-\kappa$ whenever $\|x\|_2\le\rho$, and $f_i(x)\ge-\kappa$ whenever $1\le i\le s$, $\|x\|_2\le\rho$ and $f_0(x)<\infty$. With
--   $$
--   \alpha=\min\{p_i\mid p_i>0\},\qquad \beta=\sqrt{2\rho+2\rho\sup_\nu\|y^\nu\|_2+4\kappa},
--   $$
--   $$
--   \sigma=\max\Bigl\{1,\ \sup_\nu\|y^\nu\|_2+\sqrt s\Bigl(\max\Bigl\{\kappa,\tfrac{3\beta^2}{2\alpha}\Bigr\}+\kappa\Bigr)\Bigr\},\qquad \tau=\beta\sigma,
--   $$
--   the bound (4.5) holds at each $\nu$ with $\theta^\nu\ge 9\beta^2/\alpha^2$ and $\|p^\nu-p\|_\infty\le\alpha/3$.
--
--   The paper prints $\sqrt{3/(2\alpha)}\,\beta$ in place of $3\beta^2/(2\alpha)$ in $\sigma$. The printed constant is false; a counterexample is recorded below.
--
--   The theorem quantifies how accurately the relaxed problem (4.4) solves the actual problem when the probability vector is misspecified.
--
--   **Formalization Note** The hypotheses on $\varepsilon$ and the sequences are bundled in `RateSetting`. All minimizer sets carry the domain condition of the paper. The two infimum conditions on $\kappa$ are written pointwise, and $\|\cdot\|_\infty\le\alpha/3$ coordinatewise. In item 2, $\theta^\nu=0$ is possible only with $\beta=0$, where $\tau/\sqrt{\theta^\nu}$ is read as $0$.
--
--   Differences from the source:
--
--   - correction: σ = max{1, sup‖y^ν‖₂ + √s(max{κ, √(3/(2α))β} + κ)} → σ = max{1, sup‖y^ν‖₂ + √s(max{κ, 3β²/(2α)} + κ)}; reason: the printed σ is false: for n = 1, s = 2, p = (1/2, 1/2), p^ν = (1/2 + a, 1/2 − a) with a = 2·10⁻⁵, f₀ the indicator of {0, 1000}, f₁(x) = 10⁸ − 10⁵x, f₂(x) = 100007.6x, y^ν = 0, θ^ν = 10¹², ρ = 10⁸, ε = κ = 0, every hypothesis holds, the minimizer of (4.4) has x^ν = 1000, φ(1000) − min φ = 3800 > 2η^ν ≈ 981.8 and the distance in (4.5) is 1000 > η^ν ≈ 490.9; the proof derives f_i(x) ≤ γ^ν = 3(ρ + ρ‖y^ν‖₂ + 2κ)/α ≤ 3β²/(2α) and its last line takes the square root of this bound by mistake
--   - reading: there are positive constants σ and τ such that (4.5) holds for sufficiently large θ^ν and sufficiently small ‖p^ν − p‖₂ → σ, τ > 0 and thresholds Θ > 0, δ > 0 are chosen from the fixed data and a bound Y on ‖y^ν‖₂, before ε and the sequences; reason: constants chosen after the sequences would make the claim empty whenever θ^ν is bounded; this is the stronger reading and the one the explicit constants support
--   - reading: τ/√θ^ν with θ^ν ∈ [0, ∞) and threshold θ^ν ≥ 9β²/α² → τ/√θ^ν = 0 when θ^ν = 0, which the threshold allows only if β = 0, so τ = 0; reason: the quotient 0/0 is undefined in the paper, and (4.5) holds with the value 0
--   - encoding: inf{…} ≥ −κ, α = min{p_i | p_i > 0}, sup‖y^ν‖₂, ‖p^ν − p‖_∞ ≤ α/3, dist(x, ∅) = ∞ → pointwise bounds, IsLeast, the supremum of a bounded nonempty real family, coordinatewise bounds, a distance in ℝ≥0∞; reason: equivalent forms
--   - encoding: sums containing indicator functions, under ∞ − ∞ = ∞ → definitions by cases: the formula on the feasible set, +∞ elsewhere; reason: EReal has −∞ + ∞ = −∞, and the cases give exactly the paper's values
--   - encoding: ℝⁿ, R̄, i = 1, …, s, ν ∈ ℕ = {1, 2, …}, sequential lower semicontinuity → Fin n → ℝ, EReal, Fin s, ν from 0, LowerSemicontinuous; reason: Lean conventions with the same instances; the two notions of lower semicontinuity agree on ℝⁿ
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, Theorem 4.3 and display (4.5), p.12; corrected constant from the proof of Theorem 4.3, pp.13–14

import Mathlib
import Definitions.Def_RockafellianRelax_argmin
import Definitions.Def_RockafellianRelax_epsArgmin
import Definitions.Def_RockafellianRelax_Supplement_IsProper
import Definitions.Def_RockafellianRelax_Supplement_euclidNorm
import Definitions.Def_RockafellianRelax_Supplement_euclidDist
import Definitions.Def_RockafellianRelax_Supplement_expObjective
import Definitions.Def_RockafellianRelax_Supplement_etaRate
import Definitions.Def_RockafellianRelax_Supplement_RateSetting

namespace RockafellianRelax.Supplement

/-- **Theorem 4.3 (rates in expectation minimization), with the constant σ corrected.**
Royset, Chen & Eckstrand, arXiv:2204.04762v4, Theorem 4.3, p.12: "… then there are positive constants σ and τ such that for sufficiently
large θν and sufficiently small ‖pν − p‖₂: dist(xν, (ε + 2ην)-argmin_x f₀(x) + ∑ p_i f_i(x)) ≤ ην
(4.5) … Specifically, one can take τ = βσ and σ = max{1, sup_ν ‖yν‖₂ + √s(max{κ, √(3/(2α)) β} + κ)}
… (4.5) holds for θν ≥ 9β²/α² and ‖pν − p‖_∞ ≤ α/3."

Conjunct (1) is the existence claim. Conjunct (2) is the explicit claim, with the printed
`√(3/(2α)) β` replaced by `3β²/(2α)`. The printed constant is false; the proof derives
`fᵢ(x) ≤ γν = 3(ρ + ρ‖yν‖₂ + 2κ)/α ≤ 3β²/(2α)` (pp.13–14), and its last line (p.14) misstates this
bound as `β√(3/(2α))`.

**Formalization Note.** In (1), `σ, τ`, the threshold `Θ > 0` for `θν` and the threshold `δ > 0` for
`‖pν − p‖₂` depend only on the fixed data `n, s, p, f₀, fᵢ, ρ` and on a bound `Y` of `‖yν‖₂`. They
are chosen before `ε` and the sequences. In (2), the two infimum conditions on `κ` are written
pointwise, `α` is the least positive `pᵢ`, the supremum of `‖yν‖₂` is that of a bounded nonempty
real family, and `‖pν − p‖_∞ ≤ α/3` is written coordinatewise. `dist` is in `ℝ≥0∞`, `⊤` on `∅`. -/
theorem theorem_4_3 {n s : ℕ} (f0 : (Fin n → ℝ) → EReal) (fi : Fin s → (Fin n → ℝ) → EReal)
    (p : Fin s → ℝ) (hp : p ∈ stdSimplex ℝ (Fin s))
    (hf0 : IsProper f0) (hf0lsc : LowerSemicontinuous f0)
    (hfi : ∀ i, IsProper (fi i)) (hfilsc : ∀ i, LowerSemicontinuous (fi i))
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ Y : ℝ, ∃ σ τ Θ δ : ℝ, 0 < σ ∧ 0 < τ ∧ 0 < Θ ∧ 0 < δ ∧
      ∀ (ε : ℝ) (pseq : ℕ → Fin s → ℝ) (θ : ℕ → ℝ) (y : ℕ → Fin s → ℝ)
        (z : ℕ → (Fin s → ℝ) × (Fin n → ℝ)),
        RateSetting f0 fi p ρ ε pseq θ y z → (∀ ν, euclidNorm (y ν) ≤ Y) →
        ∀ ν, Θ ≤ θ ν → euclidNorm (pseq ν - p) ≤ δ →
          euclidDist (z ν).2
              (epsArgmin (expObjective f0 fi p)
                (ε + 2 * etaRate σ τ (θ ν) (euclidNorm (pseq ν - p))))
            ≤ ENNReal.ofReal (etaRate σ τ (θ ν) (euclidNorm (pseq ν - p)))) ∧
    (∀ (ε : ℝ) (pseq : ℕ → Fin s → ℝ) (θ : ℕ → ℝ) (y : ℕ → Fin s → ℝ)
      (z : ℕ → (Fin s → ℝ) × (Fin n → ℝ)),
      RateSetting f0 fi p ρ ε pseq θ y z →
      BddAbove (Set.range fun ν => euclidNorm (y ν)) →
      ∀ κ : ℝ, 0 ≤ κ →
      (∀ x, euclidNorm x ≤ ρ → ((-κ : ℝ) : EReal) ≤ f0 x) →
      (∀ i x, euclidNorm x ≤ ρ → f0 x < ⊤ → ((-κ : ℝ) : EReal) ≤ fi i x) →
      ∀ α : ℝ, IsLeast {a : ℝ | ∃ i, 0 < p i ∧ p i = a} α →
      let Y : ℝ := ⨆ ν, euclidNorm (y ν)
      let β : ℝ := Real.sqrt (2 * ρ + 2 * ρ * Y + 4 * κ)
      let σ : ℝ := max 1 (Y + Real.sqrt s * (max κ (3 * β ^ 2 / (2 * α)) + κ))
      let τ : ℝ := β * σ
      ∀ ν, 9 * β ^ 2 / α ^ 2 ≤ θ ν → (∀ i, |pseq ν i - p i| ≤ α / 3) →
        euclidDist (z ν).2
            (epsArgmin (expObjective f0 fi p)
              (ε + 2 * etaRate σ τ (θ ν) (euclidNorm (pseq ν - p))))
          ≤ ENNReal.ofReal (etaRate σ τ (θ ν) (euclidNorm (pseq ν - p)))) := by sorry

end RockafellianRelax.Supplement
