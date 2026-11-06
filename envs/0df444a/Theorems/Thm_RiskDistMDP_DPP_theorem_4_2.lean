-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_theorem_4_2
-- name    : RiskDistMDP.DPP.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:23.554497+00:00
-- url     : https://prove2.me/theorems/3cc6c699-6954-4e00-8c1d-658c25e3a746
-- title:
--   Theorem 4.2 (corrected: $J^*_{t+1,T}$ in both argmins; Def. 2.3 (iii) weights) — finite-horizon DPP and optimal Markovian policy
-- statement:
--   Let $\gamma\in[0,1]$ and $T\in\mathbb N$. Under Assumption 2.13:
--
--   (a) for $t\in\{1,\dots,T\}$ and $x\in\mathbb X$, $\operatorname{argmin}_{\lambda\in\varpi_t(x)}G^\lambda_tJ^*_{t+1,T}(x)$ is nonempty and closed, and there is a measurable $\pi^*_t:\mathbb X\to\Lambda$ with
--   $$\pi^*_t(x)\in\operatorname*{argmin}_{\lambda\in\varpi_t(x)}G^\lambda_tJ^*_{t+1,T}(x),\qquad x\in\mathbb X;\tag{4.5}$$
--
--   (b) for every $\mathfrak p^*=(\pi^*_t)$ with measurable $\pi^*_t$ satisfying (4.5) for $t\in\{1,\dots,T\}$,
--   $$J^{\mathfrak p^*}_{t,T}=J^*_{t,T}=\inf_{\mathfrak p\in\Pi}J^{\mathfrak p}_{t,T}\ \ (0<t\le T),\qquad J^{\mathfrak p^*}_{0,T}=J^*_{0,T}=\inf_{(\mathfrak X^{\mathfrak p},\mathfrak A^{\mathfrak p})\in\Psi}\varsigma^{\mathfrak X^{\mathfrak p}}_{0,T}(\mathfrak C^{\mathfrak p}),$$
--   the last infimum over the pairs of $\Psi$ associated with some $\mathfrak p\in\Pi$.
--
--   So backward induction with $S_t$ gives the optimal values, and a measurable minimizer gives an optimal Markovian policy.
--
--   Differences from the source:
--   - correction: (a) argmin_{λ∈ϖ_t(x)} G^λ_t J*_{t,T}(x) and (4.5) with J*_{t+1,∞} → J*_{t+1,T} in both; reason: the proof and (b) use J*_{t+1,T}; with J*_{t+1,∞}, (b) fails: γ = 1/2, σ the mean, T = t = 1, a₀ costs 0 then 1 per step forever, a₁ costs 1/2 then 0; (4.5) picks a₁ (1/2 < 1) while J*_{1,1}(s) = 0 is attained only by a₀
--   - reading: t ∈ {0,…,T} and 𝔭* = (π*_t)_{t∈{0,…,T}} → t ∈ {1,…,T}; reason: ϖ_t and π_t exist only for t ∈ ℕ (§2); time 0 is the H₀ line of (b)
--   - generalization: (b) for 0 < t < T → for 0 < t ≤ T; reason: the case t = T is the start of the proof; the source statement is the case t < T
--   - reading: ρ^{𝔛^𝔭}_{0,T}(ℭ^𝔭), ρ^{𝔛^𝔭}_{0,∞}(ℭ^𝔭) → the DRM ς^{𝔛^𝔭}_{0,T}(ℭ^𝔭) of (2.9), resp. its limit (2.13) (drm0, drm0Inf); reason: ρ is defined nowhere in this role; the proofs and Proposition 5.7 use ς
--   - reading: inf_{𝔭∈Π} J^𝔭 (a function of x) → the infimum in EReal at each x; reason: the infimum of functions is pointwise
--   - reading: (𝔛^𝔭, 𝔄^𝔭) associated with 𝔭 via (2.5), ℙ(A_t ∈ B | σ(X_t)) = π_t(X_t)(B) → MarkovAssoc: ℙ(A_t ∈ B | 𝒰_t) = π_t(X_t)(B) a.s., i.e. (2.4) and (2.5) together; reason: §2.2 derives (2.5) from the Markovian property (2.4); with (2.5) alone Lemma 3.3 fails (X a singleton, A_t = A₁ a fair coin, 𝒢_t = σ(A₁), σ₂ = ess sup, T = 2: ς_{1,x,2} = 1/2 but H₁∘H₂O = 1)
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: (2.2) ℙ(X_{t+1} ∈ B | 𝒢_t) = ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) and (2.3) ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) = P(t, X_t, A_t, B) → one equation ℙ(X_{t+1} ∈ B | 𝒢_t) = P(t, X_t, A_t, B) a.s. (InPsiClass); reason: equivalent: the right side is σ(X_t) ∨ σ(A_t)-measurable and σ(X_t) ∨ σ(A_t) ⊆ 𝒢_t, so the tower property gives (2.2) and (2.3) back
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Theorem 4.2, p. 18

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_Assumption211
import Definitions.Def_RiskDistMDP_DPP_cost
import Definitions.Def_RiskDistMDP_DPP_drm
import Definitions.Def_RiskDistMDP_DPP_Jpol
import Definitions.Def_RiskDistMDP_DPP_Jstar
import Definitions.Def_RiskDistMDP_DPP_argminSet

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Theorem 4.2** (arXiv:2203.09612v4, p.18; corrected: `J*_{t+1,T}` in both argmins; finite-horizon
DPP). Let `γ ∈ [0,1]` and `T ∈ ℕ`. Under Assumption 2.13:
(a) for `t ∈ {1,…,T}` and `x ∈ 𝕏`, `argmin_{λ∈ϖ_t(x)} G^λ_t J*_{t+1,T}(x)` is nonempty and closed,
and there is a measurable `π*_t : 𝕏 → Λ` with `π*_t(x) ∈ argmin_{λ∈ϖ_t(x)} G^λ_t J*_{t+1,T}(x)`
(4.5);
(b) for `𝔭* = (π*_t)` satisfying (4.5) for all `t ∈ {1,…,T}`,
`J^{𝔭*}_{t,T} = J*_{t,T} = inf_{𝔭∈Π} J^𝔭_{t,T}` for `0 < t ≤ T`, and
`J^{𝔭*}_{0,T} = J*_{0,T} = inf_{(𝔛^𝔭,𝔄^𝔭)∈Ψ} ς^{𝔛^𝔭}_{0,T}(ℭ^𝔭)`.

**Formalization Note**
* The page writes `G^λ_t J*_{t,T}` in (a) and `J*_{t+1,∞}` in (4.5); the proof and (b) use
  `J*_{t+1,T}`. With `J*_{t+1,∞}`, (b) fails (`γ = 1/2`, `σ` the mean, `T = t = 1`: action `a₀` costs
  `0` then `1` per step forever, action `a₁` costs `1/2` then `0`; (4.5) picks `a₁`, while
  `J*_{1,1}` is attained only at `a₀`).
* `t` ranges over `{1,…,T}`: there is no `ϖ₀`, no `π₀` (§2 defines them for `t ∈ ℕ`); time `0` is
  the `H₀` line.
* (b) is stated for `0 < t ≤ T` (the page has `0 < t < T`; the case `t = T` is the start of the
  proof).
* The printed `ρ^{𝔛^𝔭}_{0,T}` is the DRM `ς^{𝔛^𝔭}_{0,T}` (2.9) (reading R2); the infima are
  pointwise in `x` (R5), in `EReal`, over exactly `Π` and over the Markov pairs of `Ψ`.
* `𝔭*` is constrained only on `{1,…,T}`. -/
theorem theorem_4_2 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hA : Assumption213 R b) (Ψ : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸))) (hΨ : Assumption211 R.toBorelMDP Pr ℱ 𝒢 Ψ)
    (T : ℕ) (hT : 1 ≤ T) :
    (∀ t, 1 ≤ t → t ≤ T → ∀ x, (argminSet R t (Jstar R T (t + 1)) x).Nonempty ∧
      IsClosed (argminSet R t (Jstar R T (t + 1)) x)) ∧
    (∀ t, 1 ≤ t → t ≤ T → ∃ π : 𝕏 → ProbabilityMeasure 𝔸, Measurable π ∧
      ∀ x, π x ∈ argminSet R t (Jstar R T (t + 1)) x) ∧
    (∀ 𝔭s : ℕ → 𝕏 → ProbabilityMeasure 𝔸,
      (∀ t, 1 ≤ t → t ≤ T → Measurable (𝔭s t) ∧ ∀ x, 𝔭s t x ∈ argminSet R t (Jstar R T (t + 1)) x) →
      (∀ t, 1 ≤ t → t ≤ T → ∀ x, Jpol R 𝔭s T t x = Jstar R T t x ∧
        ((Jstar R T t x : ℝ) : EReal) = ⨅ 𝔭 ∈ MarkovPolicies R.toBorelMDP, ((Jpol R 𝔭 T t x : ℝ) : EReal)) ∧
      Jpol0 R 𝔭s T = Jstar0 R T ∧
      Jstar0 R T = ⨅ q ∈ markovPairs R.toBorelMDP Pr ℱ 𝒢 Ψ, drm0 R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q.1 (cost R.toBorelMDP q) T) := by sorry

end RiskDistMDP.DPP
