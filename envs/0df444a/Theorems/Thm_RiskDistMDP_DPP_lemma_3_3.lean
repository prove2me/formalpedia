-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_3_3
-- name    : RiskDistMDP.DPP.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:45.947432+00:00
-- url     : https://prove2.me/theorems/432f90c6-7aa2-4866-8a04-6ae232e4b532
-- title:
--   Lemma 3.3 (corrected: Def. 2.3 (iii) weights) — the DRM of a Markov pair is a composition of policy operators
-- statement:
--   Under Assumption 2.13 (iii), (iv), let $\mathfrak p\in\Pi$ and let $(\mathfrak X^{\mathfrak p},\mathfrak A^{\mathfrak p})\in\Psi$ be associated with $\mathfrak p$. For $0<t\le T<\infty$,
--   $$\varsigma^{\mathfrak X^{\mathfrak p}}_{t,X_t,T}(\mathfrak C^{\mathfrak p})=H^{\mathfrak p}_t\circ\cdots\circ H^{\mathfrak p}_TO\,(X^{\mathfrak p}_t)\quad\mathbb P\text{-a.s.},\qquad \varsigma^{\mathfrak X^{\mathfrak p}}_{0,T}(\mathfrak C^{\mathfrak p})=H_0\circ H^{\mathfrak p}_1\circ\cdots\circ H^{\mathfrak p}_TO.$$
--
--   So the risk of a Markovian policy is computed by backward recursion on the state space, which is what makes dynamic programming possible.
--
--   Differences from the source:
--   - encoding: H^𝔭_t ∘ ⋯ ∘ H^𝔭_T O and H₀ ∘ H^𝔭_1 ∘ ⋯ ∘ H^𝔭_T O → J^𝔭_{t,T} and J^𝔭_{0,T} of (4.1) (Jpol, Jpol0); reason: (4.1) defines them as these compositions; the form is (4.2)
--   - reading: (𝔛^𝔭, 𝔄^𝔭) associated with 𝔭 via (2.5), ℙ(A_t ∈ B | σ(X_t)) = π_t(X_t)(B) → MarkovAssoc: ℙ(A_t ∈ B | 𝒰_t) = π_t(X_t)(B) a.s., i.e. (2.4) and (2.5) together; reason: §2.2 derives (2.5) from the Markovian property (2.4); with (2.5) alone Lemma 3.3 fails (X a singleton, A_t = A₁ a fair coin, 𝒢_t = σ(A₁), σ₂ = ess sup, T = 2: ς_{1,x,2} = 1/2 but H₁∘H₂O = 1)
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - generalization: (Ω, ℋ, ℙ) a complete probability space without atoms → any probability space; completeness follows from ℱ₁ ⊆ ℋ containing all ℙ-negligible sets; atomlessness is not assumed; reason: no step of the result uses atomlessness (only §2.3’s quantile transform and Remark 2.5 do); every atomless complete space is a special case
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: a regular version P^{Y|𝒰_t} of ℙ(Y ∈ · | 𝒰_t), to which σ_{t,x} is applied → Mathlib’s condDistrib Y id (a fixed version), with σ_{t,x} applied when it lies in 𝒫_b(ℝ) and 0 otherwise (guardσ); reason: every claim about the DRM is ℙ-a.s., and the conditional distributions of the bounded variables involved lie in 𝒫_b(ℝ) for a.e. ω, so the version and the guard change the DRM only on a null set
--   - encoding: (2.2) ℙ(X_{t+1} ∈ B | 𝒢_t) = ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) and (2.3) ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) = P(t, X_t, A_t, B) → one equation ℙ(X_{t+1} ∈ B | 𝒢_t) = P(t, X_t, A_t, B) a.s. (InPsiClass); reason: equivalent: the right side is σ(X_t) ∨ σ(A_t)-measurable and σ(X_t) ∨ σ(A_t) ⊆ 𝒢_t, so the tower property gives (2.2) and (2.3) back
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 3.3, p. 16; (4.2), p. 18

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_Assumption211
import Definitions.Def_RiskDistMDP_DPP_cost
import Definitions.Def_RiskDistMDP_DPP_drm
import Definitions.Def_RiskDistMDP_DPP_Jpol

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 3.3** (arXiv:2203.09612v4, p.16; with (4.2), p.18). Under Assumption 2.13 (iii), (iv), for
a Markovian policy `𝔭 ∈ Π`, a pair `(𝔛^𝔭, 𝔄^𝔭) ∈ Ψ` associated with `𝔭` and `0 < t ≤ T < ∞`,
`ς^{𝔛^𝔭}_{t,X_t,T}(ℭ^𝔭) = H^𝔭_t ∘ ⋯ ∘ H^𝔭_T O(X^𝔭_t)` `ℙ`-a.s., and
`ς^{𝔛^𝔭}_{0,T}(ℭ^𝔭) = H₀ ∘ H^𝔭_1 ∘ ⋯ ∘ H^𝔭_T O`.

**Formalization Note** The compositions are written as the value functions of (4.1),
`J^𝔭_{t,T} = H^𝔭_t ∘ ⋯ ∘ H^𝔭_T O` and `J^𝔭_{0,T} = H₀ J^𝔭_{1,T}`, i.e. in the form (4.2).
Association is the reading R1 (`MarkovAssoc`: conditioning on `𝒰_t`). -/
theorem lemma_3_3 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (hinfo : IsInfoSetting Pr ℱ 𝒢)
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (b : ℕ → ℝ) (hiii : A213iii R.σ)
    (hiv : A213iv R.toBorelMDP b) (Ψ : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸))) (hΨ : Assumption211 R.toBorelMDP Pr ℱ 𝒢 Ψ)
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (h𝔭 : 𝔭 ∈ MarkovPolicies R.toBorelMDP)
    (q : (ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸)) (hq : q ∈ Ψ) (hassoc : MarkovAssoc Pr ℱ 𝒢 𝔭 q) :
    (∀ t T : ℕ, 0 < t → t ≤ T → ∀ᵐ ω ∂Pr,
      drm R.σ R.γ Pr (decInfo ℱ 𝒢) q.1 (cost R.toBorelMDP q) T t (q.1 t ω) ω = ((Jpol R 𝔭 T t (q.1 t ω) : ℝ) : EReal)) ∧
    (∀ T : ℕ, 1 ≤ T → drm0 R.σ0 R.σ R.γ Pr (decInfo ℱ 𝒢) q.1 (cost R.toBorelMDP q) T = Jpol0 R 𝔭 T) := by sorry

end RiskDistMDP.DPP
