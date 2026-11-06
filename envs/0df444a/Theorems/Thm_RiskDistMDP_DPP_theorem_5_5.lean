-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_theorem_5_5
-- name    : RiskDistMDP.DPP.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:29.401321+00:00
-- url     : https://prove2.me/theorems/c8bd9f0c-8262-4532-b4d7-bbd257e1223a
-- title:
--   Theorem 5.5 and Proposition 5.7 (corrected: Def. 2.3 (iii) weights; one cost bound $b$) — infinite-horizon DPP: unique bounded Bellman solution, optimal Markovian policy beats every pair
-- statement:
--   Let $\mathbb X,\mathbb A$ be complete separable metric spaces, $(\Omega,\mathcal H,\mathbb P)$ a probability space with filtrations $\mathbb F\subseteq\mathbb G$ and decision information $\mathcal U_t$, and $\Psi$ a set of state–action pairs satisfying Assumption 2.11. Let $\sigma_0$ and $(\sigma_{t,x})$ satisfy Definition 2.3 and Assumption 2.6. Suppose $\gamma\in[0,1)$, $(\sigma_{t,x})$ is normalized, and Assumption 2.13 holds with one cost bound $b$. Then:
--
--   (a) for every $t\in\mathbb N$,
--   $$J^*_{t,\infty}=S_tJ^*_{t+1,\infty},$$
--   and every $(J'_{t,\infty})_{t\in\mathbb N}\in\ell^\infty(\mathbb N;\mathbb X,\mathcal B(\mathbb X))$ with $J'_{t,\infty}=S_tJ'_{t+1,\infty}$ for all $t$ equals $(J^*_{t,\infty})_{t\in\mathbb N}$;
--
--   (b) for $t\in\mathbb N$ and $x\in\mathbb X$, $\operatorname{argmin}_{\lambda\in\varpi_t(x)}G^\lambda_tJ^*_{t+1,\infty}(x)$ is nonempty and closed, and there is a measurable $\pi^*_t:\mathbb X\to\Lambda$ with
--   $$\pi^*_t(x)\in\operatorname*{argmin}_{\lambda\in\varpi_t(x)}G^\lambda_tJ^*_{t+1,\infty}(x),\qquad x\in\mathbb X;\tag{5.7}$$
--
--   (c) for every $\mathfrak p^*=(\pi^*_t)$ with measurable $\pi^*_t$ satisfying (5.7) for all $t\in\mathbb N$,
--   $$J^{\mathfrak p^*}_{t,\infty}=J^*_{t,\infty}=\inf_{\mathfrak p\in\Pi}J^{\mathfrak p}_{t,\infty}\ (t\in\mathbb N),\qquad J^{\mathfrak p^*}_{0,\infty}=H_0J^*_{1,\infty}=\inf_{(\mathfrak X^{\mathfrak p},\mathfrak A^{\mathfrak p})\in\Psi}\varsigma^{\mathfrak X^{\mathfrak p}}_{0,\infty}(\mathfrak C^{\mathfrak p}),$$
--   the last infimum over the pairs of $\Psi$ associated with some $\mathfrak p\in\Pi$;
--
--   (Proposition 5.7) for every $(\mathfrak X,\mathfrak A)\in\Psi$,
--   $$\inf_{(\mathfrak X^{\mathfrak p},\mathfrak A^{\mathfrak p})\in\Psi}\varsigma^{\mathfrak X^{\mathfrak p}}_{0,\infty}(\mathfrak C^{\mathfrak p})\le\varsigma^{\mathfrak X}_{0,\infty}(\mathfrak C).$$
--
--   Together: the optimal value is the unique bounded solution of the risk-averse Bellman equation, a measurable selector of minimizers is an optimal Markovian policy, and no pair of $\Psi$, history-dependent or randomized, does better.
--
--   Differences from the source:
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - correction: Assumption 2.13 (iv): for any t, ‖C_t‖_∞ ≤ b for some b > 0 (b may depend on t) → one constant b for all t (A213iv with fun _ => b); reason: with a t-dependent bound the infinite-horizon results fail (𝕏, 𝔸 singletons, γ = 1/2, C_t ≡ 4^t, σ the mean: J*_{t,T} diverges); §5 bounds the values by b/(1−γ), one constant
--   - reading: (𝔛^𝔭, 𝔄^𝔭) associated with 𝔭 via (2.5), ℙ(A_t ∈ B | σ(X_t)) = π_t(X_t)(B) → MarkovAssoc: ℙ(A_t ∈ B | 𝒰_t) = π_t(X_t)(B) a.s., i.e. (2.4) and (2.5) together; reason: §2.2 derives (2.5) from the Markovian property (2.4); with (2.5) alone Lemma 3.3 fails (X a singleton, A_t = A₁ a fair coin, 𝒢_t = σ(A₁), σ₂ = ess sup, T = 2: ς_{1,x,2} = 1/2 but H₁∘H₂O = 1)
--   - reading: ρ^{𝔛^𝔭}_{0,T}(ℭ^𝔭), ρ^{𝔛^𝔭}_{0,∞}(ℭ^𝔭) → the DRM ς^{𝔛^𝔭}_{0,T}(ℭ^𝔭) of (2.9), resp. its limit (2.13) (drm0, drm0Inf); reason: ρ is defined nowhere in this role; the proofs and Proposition 5.7 use ς
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - reading: Assumption 2.13 (i): x^n → x⁰, a^n → a⁰ imply ∫_ℝ f(y)P(t,x^n,a^n,dy) → ∫_ℝ f(y)P(t,x,a,dy), f ∈ C_b(𝕏) → continuity of (x, a) ↦ P(t, x, a, ·) into ProbabilityMeasure 𝕏 (A213i); reason: the first line says weakly continuous; the integrals are over 𝕏 with P(t,x⁰,a⁰,dy) on the right; sequential and topological continuity agree on the metrizable 𝕏 × 𝔸
--   - reading: inf_{𝔭∈Π} J^𝔭 (a function of x) → the infimum in EReal at each x; reason: the infimum of functions is pointwise
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: a regular version P^{Y|𝒰_t} of ℙ(Y ∈ · | 𝒰_t), to which σ_{t,x} is applied → Mathlib’s condDistrib Y id (a fixed version), with σ_{t,x} applied when it lies in 𝒫_b(ℝ) and 0 otherwise (guardσ); reason: every claim about the DRM is ℙ-a.s., and the conditional distributions of the bounded variables involved lie in 𝒫_b(ℝ) for a.e. ω, so the version and the guard change the DRM only on a null set
--   - encoding: (2.2) ℙ(X_{t+1} ∈ B | 𝒢_t) = ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) and (2.3) ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) = P(t, X_t, A_t, B) → one equation ℙ(X_{t+1} ∈ B | 𝒢_t) = P(t, X_t, A_t, B) a.s. (InPsiClass); reason: equivalent: the right side is σ(X_t) ∨ σ(A_t)-measurable and σ(X_t) ∨ σ(A_t) ⊆ 𝒢_t, so the tower property gives (2.2) and (2.3) back
--   - encoding: ℓ^∞(𝕏, ℬ(𝕏)), ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and bounds through ‖·‖_∞ → IsLinf / IsLinfSeq (measurable and uniformly bounded) and bounds stated for every c with |·| ≤ c; reason: equivalent: take c = ‖·‖_∞
--   - encoding: lim_{T→∞} in (2.13), (5.1), (5.4) → limUnder atTop, pointwise, in ℝ for t ≥ 1 and in EReal at time 0; reason: the limits exist under the hypotheses (Lemmas 2.9, 5.1, 5.3), so limUnder is the limit
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Theorem 5.5, p. 23; Proposition 5.7, p. 24

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_Assumption211
import Definitions.Def_RiskDistMDP_DPP_cost
import Definitions.Def_RiskDistMDP_DPP_drmInf
import Definitions.Def_RiskDistMDP_DPP_JpolInf
import Definitions.Def_RiskDistMDP_DPP_JstarInf
import Definitions.Def_RiskDistMDP_DPP_S
import Definitions.Def_RiskDistMDP_DPP_argminSet
import Definitions.Def_RiskDistMDP_DPP_IsLinf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Theorem 5.5 and Proposition 5.7** (arXiv:2203.09612v4, pp.23–24; infinite-horizon DPP).
Suppose `γ ∈ [0,1)` and `(σ_{t,x})` is normalized. Under Assumption 2.13:
(a) `J*_{t,∞} = S_t J*_{t+1,∞}` for `t ∈ ℕ`, and every `(J′_{t,∞})_{t∈ℕ} ∈ ℓ^∞(ℕ; 𝕏, ℬ(𝕏))` with
`J′_{t,∞} = S_t J′_{t+1,∞}` equals `(J*_{t,∞})_{t∈ℕ}`;
(b) for `t ∈ ℕ` and `x ∈ 𝕏`, `argmin_{λ∈ϖ_t(x)} G^λ_t J*_{t+1,∞}(x)` is nonempty and closed, and there
is a measurable `π*_t : 𝕏 → Λ` with `π*_t(x) ∈ argmin_{λ∈ϖ_t(x)} G^λ_t J*_{t+1,∞}(x)` (5.7);
(c) for every `𝔭* = (π*_t)` satisfying (5.7) for all `t ∈ ℕ`,
`J^{𝔭*}_{t,∞} = J*_{t,∞} = inf_{𝔭∈Π} J^𝔭_{t,∞}` for `t ∈ ℕ`, and
`J^{𝔭*}_{0,∞} = H₀ J*_{1,∞} = inf_{(𝔛^𝔭,𝔄^𝔭)∈Ψ} ς^{𝔛^𝔭}_{0,∞}(ℭ^𝔭)`;
(Proposition 5.7) for every `(𝔛, 𝔄) ∈ Ψ`, `inf_{(𝔛^𝔭,𝔄^𝔭)∈Ψ} ς^{𝔛^𝔭}_{0,∞}(ℭ^𝔭) ≤ ς^𝔛_{0,∞}(ℭ)`.

**Formalization Note**
* The standing assumptions are those of the paper: Definition 2.3 for `σ₀` and every `σ_{t,x}`
  (with the corrected axiom (iii)), Assumption 2.6, the model conditions of §2 (`P` measurable,
  `𝒜_t` nonempty closed valued and weakly measurable, `C_t` Borel), `γ ∈ [0,1]`, the information
  structure, and Assumption 2.11 for `Ψ`. No hypothesis is placed on `σ₀` beyond Definition 2.3.
* The cost bound `b` is one constant for all `t` (Assumption 2.13 (iv) as used throughout §5).
* The printed `ρ^{𝔛^𝔭}_{0,∞}` is the DRM `ς^{𝔛^𝔭}_{0,∞}` (2.13) (reading R2). The infima are in
  `EReal`, pointwise in `x` for `t ∈ ℕ` (R5), over exactly `Π` and over the pairs of `Ψ` associated
  with some `𝔭 ∈ Π` (`markovPairs`, association in the sense R1). Proposition 5.7 compares with every
  pair of `Ψ`, history-dependent and randomized included.
* `ℓ^∞(ℕ; 𝕏, ℬ(𝕏))` is `IsLinfSeq`; every selector policy `𝔭*` is quantified, as printed. -/
theorem theorem_5_5 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (hγ : R.γ < 1) (hnorm : R.Normalized) (b : ℝ)
    (hA : Assumption213 R (fun _ => b)) (Ψ : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸))) (hΨ : Assumption211 R.toBorelMDP Pr ℱ 𝒢 Ψ) :
    (∀ t, 1 ≤ t → ∀ x, ((JstarInf R t x : ℝ) : EReal) = S R t (JstarInf R (t + 1)) x) ∧
    (∀ J' : ℕ → 𝕏 → ℝ, IsLinfSeq J' →
      (∀ t, 1 ≤ t → ∀ x, ((J' t x : ℝ) : EReal) = S R t (J' (t + 1)) x) →
      ∀ t, 1 ≤ t → J' t = JstarInf R t) ∧
    (∀ t, 1 ≤ t → ∀ x, (argminSet R t (JstarInf R (t + 1)) x).Nonempty ∧ IsClosed (argminSet R t (JstarInf R (t + 1)) x)) ∧
    (∀ t, 1 ≤ t → ∃ π : 𝕏 → ProbabilityMeasure 𝔸, Measurable π ∧
      ∀ x, π x ∈ argminSet R t (JstarInf R (t + 1)) x) ∧
    (∀ 𝔭s : ℕ → 𝕏 → ProbabilityMeasure 𝔸,
      (∀ t, 1 ≤ t → Measurable (𝔭s t) ∧ ∀ x, 𝔭s t x ∈ argminSet R t (JstarInf R (t + 1)) x) →
      (∀ t, 1 ≤ t → ∀ x, JpolInf R 𝔭s t x = JstarInf R t x ∧
        ((JstarInf R t x : ℝ) : EReal) = ⨅ 𝔭 ∈ MarkovPolicies R.toBorelMDP, ((JpolInf R 𝔭 t x : ℝ) : EReal)) ∧
      Jpol0Inf R 𝔭s = H0 R (JstarInf R 1) ∧
      H0 R (JstarInf R 1) = ⨅ q ∈ markovPairs R.toBorelMDP Pr ℱ 𝒢 Ψ, drm0Inf R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q.1 (cost R.toBorelMDP q)) ∧
    (∀ q ∈ Ψ, (⨅ q' ∈ markovPairs R.toBorelMDP Pr ℱ 𝒢 Ψ, drm0Inf R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q'.1 (cost R.toBorelMDP q')) ≤ drm0Inf R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q.1 (cost R.toBorelMDP q)) := by sorry

end RiskDistMDP.DPP
