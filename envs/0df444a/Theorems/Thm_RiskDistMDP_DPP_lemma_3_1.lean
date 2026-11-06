-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_lemma_3_1
-- name    : RiskDistMDP.DPP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:33.225978+00:00
-- url     : https://prove2.me/theorems/7ebb9854-deb3-4d24-85d9-f43dbb72937f
-- title:
--   Lemma 3.1 (corrected: shift $\gamma a$; Def. 2.3 (iii) weights) — monotonicity, range and translation of $G^\lambda_t$ and $H_0$
-- statement:
--   Let $t\in\mathbb N$ and $\lambda\in\Lambda$.
--
--   (a) Under Assumption 2.13 (iv) with cost bound $b_t$: if $v^1\le v^2$ in $\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$ then $G^\lambda_tv^1\le G^\lambda_tv^2$; if $\sigma_{t,x}$ is normalized for every $x$ and $|v|\le c$, then
--   $$G^\lambda_tv(x)\in[-b_t-\gamma c,\ b_t+\gamma c];$$
--   and without normalization, with the constants $b^\sigma_t$ of Assumption 2.6, $G^\lambda_tv(x)\in[-b^\sigma_t-b_t-\gamma c,\ b^\sigma_t+b_t+\gamma c]$.
--
--   (b) For $a\in\mathbb R$ and $v\in\ell^\infty$, at every $x$ with $\widetilde P^v_{t,x,\lambda}\in\mathcal P_b(\mathbb R)$,
--   $$G^\lambda_t(a+v)(x)=\gamma a+G^\lambda_tv(x).$$
--
--   For $H_0$: it is monotone, $H_0(a+v)=\gamma a+H_0v$, and $H_0v\in[-\gamma c,\gamma c]$ when $\sigma_0$ is normalized and $|v|\le c$.
--
--   These are the order and translation properties every later estimate uses.
--
--   Differences from the source:
--   - correction: G^λ_t(a + v) = a + G^λ_t v (and the same for H₀) → G^λ_t(a + v) = γa + G^λ_t v and H₀(a + v) = γa + H₀ v; reason: by (3.3) the shift enters as γa: with γ = 1/2, σ_{t,x} the mean, C_t ≡ 0, v ≡ 0, a = 1 the left side is 1/2 and the printed right side 1 (proved in the sanity file)
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - reading: (b) for every v ∈ ℓ^∞ (σ_{t,x} is defined on 𝒫_b(ℝ) only) → at every x where P̃^v_{t,x,λ} ∈ 𝒫_b(ℝ); reason: G^λ_t v(x) is defined only there; under Assumption 2.13 (iv) this is every x
--   - generalization: (a) the range under normalization → an added conjunct: the range [−b^σ_t − b_t − γc, b^σ_t + b_t + γc] without normalization, b^σ_t from Assumption 2.6; reason: it makes the finiteness of G^λ_t explicit; dropping the conjunct gives the source statement
--   - reading: Properties for H₀ hold analogously → monotonicity, shift γa, and the range [−γ‖v‖_∞, γ‖v‖_∞] under σ₀(δ₀) = 0; reason: H₀ has no cost term; σ₀ is outside "normalized" (p.9), so the range clause needs its own normalization
--   - reading: (3.1): P̃^v_0 the law of γv(Y), Y ∼ ξ₁ → Y ∼ μ (lawH0); reason: ξ₁ is defined nowhere; μ is the law of X₁ (Assumption 2.11 (i))
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: ℓ^∞(𝕏, ℬ(𝕏)), ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and bounds through ‖·‖_∞ → IsLinf / IsLinfSeq (measurable and uniformly bounded) and bounds stated for every c with |·| ≤ c; reason: equivalent: take c = ‖·‖_∞
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Lemma 3.1, p. 15

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_G
import Definitions.Def_RiskDistMDP_DPP_H0
import Definitions.Def_RiskDistMDP_DPP_IsLinf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Lemma 3.1** (arXiv:2203.09612v4, p.15; corrected: the shift is `γa`). For every `(t, λ) ∈ ℕ × Λ`:
(a) under Assumption 2.13 (iv), `v¹ ≤ v²` in `ℓ^∞(𝕏, ℬ(𝕏))` implies `G^λ_t v¹ ≤ G^λ_t v²`, and if
`σ_{t,x}` is normalized for `x ∈ 𝕏` then `G^λ_t v(x) ∈ [−b − γ‖v‖_∞, b + γ‖v‖_∞]`;
(b) for `a ∈ ℝ` and `v ∈ ℓ^∞(𝕏, ℬ(𝕏))`, `G^λ_t(a + v) = γa + G^λ_t v`.
The properties for `H₀` hold analogously.

**Formalization Note**
* The page prints `G^λ_t(a + v) = a + G^λ_t v`; by (3.3) the shift enters as `γa` (with `γ = 1/2`,
  `σ_{t,x}` the mean, `C_t ≡ 0`, `v ≡ 0`, `a = 1` the left side is `1/2`, the printed right side `1`).
* `b` is the cost bound `b t` of Assumption 2.13 (iv) at time `t`; `‖v‖_∞` enters through any `c`
  with `|v| ≤ c`.
* (b) is stated at the states `x` where `P̃^v_{t,x,λ} ∈ 𝒫_b(ℝ)`, the domain of `σ_{t,x}` (it holds
  for every `x` under Assumption 2.13 (iv)).
* The third clause of (a) (range without normalization, from Assumption 2.6) is added: it is what
  makes the values of `G^λ_t` finite.
* "Analogously" for `H₀` is spelled out: monotone, shift `γa`, and range `[−γ‖v‖_∞, γ‖v‖_∞]` when
  `σ₀` is normalized (normalization of `(σ_{t,x})` says nothing about `σ₀`). -/
theorem lemma_3_1 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (t : ℕ) (ht : 1 ≤ t) (l : ProbabilityMeasure 𝔸) :
    (∀ b : ℕ → ℝ, A213iv R.toBorelMDP b →
      (∀ v₁ v₂ : 𝕏 → ℝ, IsLinf v₁ → IsLinf v₂ → v₁ ≤ v₂ → ∀ x, G R t l v₁ x ≤ G R t l v₂ x) ∧
      ((∀ x, Normalized (R.σ t x)) → ∀ v : 𝕏 → ℝ, IsLinf v → ∀ c : ℝ, (∀ y, |v y| ≤ c) → ∀ x,
        ((-(b t) - R.γ * c : ℝ) : EReal) ≤ G R t l v x ∧
          G R t l v x ≤ ((b t + R.γ * c : ℝ) : EReal)) ∧
      (∀ bσ : ℕ → ℝ, SigmaBounded R.σ bσ → ∀ v : 𝕏 → ℝ, IsLinf v → ∀ c : ℝ, (∀ y, |v y| ≤ c) →
        ∀ x, ((-(bσ t) - b t - R.γ * c : ℝ) : EReal) ≤ G R t l v x ∧
          G R t l v x ≤ ((bσ t + b t + R.γ * c : ℝ) : EReal))) ∧
    (∀ (a : ℝ) (v : 𝕏 → ℝ), IsLinf v → ∀ x, InPb (lawG R t x l v) →
      G R t l (fun y => a + v y) x = ((R.γ * a : ℝ) : EReal) + G R t l v x) ∧
    (∀ v₁ v₂ : 𝕏 → ℝ, IsLinf v₁ → IsLinf v₂ → v₁ ≤ v₂ → H0 R v₁ ≤ H0 R v₂) ∧
    (∀ (a : ℝ) (v : 𝕏 → ℝ), IsLinf v →
      H0 R (fun y => a + v y) = ((R.γ * a : ℝ) : EReal) + H0 R v) ∧
    (Normalized R.σ0 → ∀ v : 𝕏 → ℝ, IsLinf v → ∀ c : ℝ, (∀ y, |v y| ≤ c) →
      ((-(R.γ * c) : ℝ) : EReal) ≤ H0 R v ∧ H0 R v ≤ ((R.γ * c : ℝ) : EReal)) := by sorry

end RiskDistMDP.DPP
