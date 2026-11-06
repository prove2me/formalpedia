-- Prove2me | Theorems.Thm_RiskDistMDP_DPP_proposition_5_2
-- name    : RiskDistMDP.DPP.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:30.282815+00:00
-- url     : https://prove2.me/theorems/f8506260-02e7-43ae-ac61-8ca141aa1f2b
-- title:
--   Proposition 5.2 (corrected: one cost bound $b$; Def. 2.3 (iii) weights) — $\mathfrak H^{\mathfrak p}$ is a $\gamma$-contraction with fixed point $J^{\mathfrak p}_\infty$
-- statement:
--   Suppose $\gamma\in[0,1)$ and $(\sigma_{t,x})$ is normalized, and Assumption 2.13 (iv) holds with one bound $b$. For every $\mathfrak p\in\Pi$:
--
--   1. $\mathfrak H^{\mathfrak p}$ maps $\ell^\infty(\mathbb N;\mathbb X,\mathcal B(\mathbb X))$ into itself (the values $H^{\mathfrak p}_tv_{t+1}(x)$ are finite);
--   2. if $|v_t-w_t|\le c$ for all $t\in\mathbb N$, then $|(\mathfrak H^{\mathfrak p}\mathfrak v)_t-(\mathfrak H^{\mathfrak p}\mathfrak w)_t|\le\gamma c$ for all $t$;
--   3. $(J^{\mathfrak p}_{t,\infty})_{t\in\mathbb N}$ lies in $\ell^\infty(\mathbb N;\mathbb X,\mathcal B(\mathbb X))$ and is a fixed point of $\mathfrak H^{\mathfrak p}$;
--   4. it is the only fixed point there.
--
--   Differences from the source:
--   - correction: Assumption 2.13 (iv): for any t, ‖C_t‖_∞ ≤ b for some b > 0 (b may depend on t) → one constant b for all t (A213iv with fun _ => b); reason: with a t-dependent bound the infinite-horizon results fail (𝕏, 𝔸 singletons, γ = 1/2, C_t ≡ 4^t, σ the mean: J*_{t,T} diverges); §5 bounds the values by b/(1−γ), one constant
--   - reading: ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) as sequences of v_t : (𝕏, ℬ(ℝ)) → (ℝ, ℬ(ℝ)) → sequences of ℬ(𝕏)-measurable functions; reason: ℬ(ℝ) on 𝕏 is a typo; the notation ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and §2 have ℬ(𝕏)
--   - encoding: ℌ^𝔭 is a γ-contraction mapping on ℓ^∞(ℕ; 𝕏, ℬ(𝕏)); unique fixed point → self-map with finite values, |ℌv − ℌw| ≤ γc whenever |v − w| ≤ c, γ < 1; fixed point in the space and uniqueness in the space; reason: the same statement with the sup norm unfolded
--   - correction: σ₀ and every σ_{t,x} satisfy Definition 2.3 with (iii) σ(ζ_θ) ≤ θσ(ζ₀) + (1−θ)σ(ζ₁) → IsDistRiskMeasure, whose (iii) reads σ(ζ_θ) ≤ (1−θ)σ(ζ₀) + θσ(ζ₁); reason: as printed, (iii) at θ = 0, ζ = δ_{(1,0)} gives σ(δ₁) ≤ σ(δ₀) while (i) gives σ(δ₁) = σ(δ₀) + 1, so σ(δ₀) = +∞ for every such σ, contradicting Assumption 2.6: every statement would be vacuous; the corrected weights are those of Definition 2.2 (iii) and Remark 2.5
--   - encoding: 𝕏, 𝔸 complete separable metric spaces with Borel σ-algebras; Λ and 𝒫(K) with the Borel σ-algebras of the weak topology → Polish spaces with BorelSpace; ProbabilityMeasure with its weak topology and Mathlib’s Giry (evaluation) σ-algebra, on Λ and on 𝒫(K) ⊂ Measure ℝ; reason: Polish means separable and completely metrizable, and every hypothesis is topological; the Borel and evaluation σ-algebras coincide (p.5, Lemma B.5)
--   - encoding: times t ∈ ℕ = {1, 2, …} → t : ℕ with 1 ≤ t; index 0 is unused (C₀ ≡ 0 is built into the cost process); reason: same index set
--   - encoding: σ with values in (−∞, ∞]; G^λ_t, H^𝔭_t, S_t, J map into ℓ^∞; H₀ real-valued → operators valued in EReal; finite-horizon value functions real via .toReal of the EReal operator values; H₀ and all time-0 quantities kept in EReal; reason: the operator values are finite under the hypotheses (Lemma 3.1, stated in lemma_3_1); σ₀ is not covered by Assumption 2.6 and may be +∞, so time-0 quantities stay in EReal
--   - encoding: ℓ^∞(𝕏, ℬ(𝕏)), ℓ^∞(ℕ; 𝕏, ℬ(𝕏)) and bounds through ‖·‖_∞ → IsLinf / IsLinfSeq (measurable and uniformly bounded) and bounds stated for every c with |·| ≤ c; reason: equivalent: take c = ‖·‖_∞
--   - encoding: lim_{T→∞} in (2.13), (5.1), (5.4) → limUnder atTop, pointwise, in ℝ for t ≥ 1 and in EReal at time 0; reason: the limits exist under the hypotheses (Lemmas 2.9, 5.1, 5.3), so limUnder is the limit
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, Proposition 5.2, p. 22

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_Assumption213
import Definitions.Def_RiskDistMDP_DPP_MarkovPolicies
import Definitions.Def_RiskDistMDP_DPP_JpolInf
import Definitions.Def_RiskDistMDP_DPP_polSeqOp
import Definitions.Def_RiskDistMDP_DPP_IsLinf

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace RiskDistMDP.DPP

/-- **Proposition 5.2** (arXiv:2203.09612v4, p.22). Suppose `γ ∈ [0,1)` and `(σ_{t,x})` is normalized.
Under Assumption 2.13 (iv), for every Markovian policy `𝔭 ∈ Π`, `ℌ^𝔭` is a `γ`-contraction on
`ℓ^∞(ℕ; 𝕏, ℬ(𝕏))`, and `(J^𝔭_{t,∞})_{t∈ℕ}` is the unique fixed point of `ℌ^𝔭`.

**Formalization Note** "`γ`-contraction on `ℓ^∞(ℕ; 𝕏, ℬ(𝕏))`" is written as: `ℌ^𝔭` maps the bounded
measurable sequences into themselves (with finite values of `H^𝔭_t`), and
`|(ℌ^𝔭𝔳)_t(x) − (ℌ^𝔭𝔴)_t(x)| ≤ γc` whenever `|v_t − w_t| ≤ c` for all `t ∈ ℕ` (i.e.
`‖ℌ^𝔭𝔳 − ℌ^𝔭𝔴‖_∞ ≤ γ‖𝔳 − 𝔴‖_∞`), with `γ < 1`. "Unique fixed point" is: `(J^𝔭_{t,∞})` is in the
space, is a fixed point, and every fixed point in the space equals it. The page's
`v_t : (𝕏, ℬ(ℝ)) → (ℝ, ℬ(ℝ))` is read as `ℬ(𝕏)`-measurable. -/
theorem proposition_5_2 {𝕏 𝔸 : Type*} [TopologicalSpace 𝕏] [PolishSpace 𝕏] [MeasurableSpace 𝕏] [BorelSpace 𝕏]
    [TopologicalSpace 𝔸] [PolishSpace 𝔸] [MeasurableSpace 𝔸] [BorelSpace 𝔸]
    (R : RiskMDP 𝕏 𝔸) (hR : R.Standing) (hγ : R.γ < 1) (hnorm : R.Normalized) (b : ℝ)
    (hiv : A213iv R.toBorelMDP (fun _ => b))
    (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸) (h𝔭 : 𝔭 ∈ MarkovPolicies R.toBorelMDP) :
    (∀ v : ℕ → 𝕏 → ℝ, IsLinfSeq v → IsLinfSeq (polSeqOp R 𝔭 v) ∧
      ∀ t, 1 ≤ t → ∀ x, H R 𝔭 t (v (t + 1)) x ≠ ⊤ ∧ H R 𝔭 t (v (t + 1)) x ≠ ⊥) ∧
    (∀ v w : ℕ → 𝕏 → ℝ, IsLinfSeq v → IsLinfSeq w → ∀ c : ℝ,
      (∀ t, 1 ≤ t → ∀ x, |v t x - w t x| ≤ c) →
      ∀ t, 1 ≤ t → ∀ x, |polSeqOp R 𝔭 v t x - polSeqOp R 𝔭 w t x| ≤ R.γ * c) ∧
    IsLinfSeq (JpolInf R 𝔭) ∧
    (∀ t, 1 ≤ t → polSeqOp R 𝔭 (JpolInf R 𝔭) t = JpolInf R 𝔭 t) ∧
    (∀ v : ℕ → 𝕏 → ℝ, IsLinfSeq v → (∀ t, 1 ≤ t → polSeqOp R 𝔭 v t = v t) →
      ∀ t, 1 ≤ t → v t = JpolInf R 𝔭 t) := by sorry

end RiskDistMDP.DPP
