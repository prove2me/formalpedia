-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_4_1
-- name    : SpatialHalfspace.FullLabels.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:23.275872+00:00
-- url     : https://prove2.me/theorems/804e25d0-934e-4d57-8c2b-d078a3ecf145
-- title:
--   Lemma 4.1 — Information lower bound for approximate recovery
-- statement:
--   Let $k\ge 1$ be an integer, let $\Psi\in\{0,1\}^k$ be conditionally uniform given $S$, and let $\hat\Psi$ be a function of $(S,T)$. If
--
--   $$\Pr\big[d_H(\Psi,\hat\Psi)\le r\big]\ \ge\ \gamma,$$
--
--   where $r$ is an integer with $0\le r\le k/2$ and $\gamma\in(0,1]$, then
--
--   $$I(\Psi;T\mid S)\ \ge\ \gamma k\big(1-h_2(r/k)\big)-1,$$
--
--   with $I$ and $h_2$ in bits. This Fano-type bound converts approximate recovery into a lower bound on the information carried by $T$.
--
--   **Formalization Note** The right-hand side is compared as an extended nonnegative real (`ENNReal.ofReal`), so a negative right-hand side is the trivial bound $0$.
--
--   Differences from the source:
--
--   - encoding: Ψ conditionally uniform given S → Ψ uniform on {0,1}^k and independent of S; reason: conditional uniformity given S is equivalent to this
--   - encoding: Ψ̂ a function of (S, T); Shannon information in bits → Ψ̂ = g(S, T) for a measurable g; measurable random variables on arbitrary measurable spaces; conditional information is the supremum of finite-observation KL divergences in bits; reason: finite measurable quantization defines Shannon conditional information without requiring a regular conditional law of the original observation T; no source observation is excluded
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 10, PDF p. 11, Lemma 4.1, PDF p. 11 (proof in App. A.4, PDF pp. 15–16)

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma 4.1 (Information lower bound for approximate recovery), printed p. 10. For `k ≥ 1`,
`Ψ ∈ {0,1}^k` conditionally uniform given `S` (uniform and independent of `S`), and
`Ψ̂ = g(S, T)`: if `Pr[d_H(Ψ, Ψ̂) ≤ r] ≥ γ` with an integer `0 ≤ r ≤ k/2` and `γ ∈ (0,1]`, then
`I(Ψ; T | S) ≥ γk(1 − h₂(r/k)) − 1` (bits). -/
theorem lemma_4_1 {Ω σT τT : Type} [MeasurableSpace Ω] [MeasurableSpace σT] [MeasurableSpace τT]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (k : ℕ) (hk : 1 ≤ k) (Ψ : Ω → (Fin k → Bool)) (S : Ω → σT) (T : Ω → τT)
    (hΨ : Measurable Ψ) (hS : Measurable S) (hT : Measurable T)
    (hunif : μ.map Ψ = uniformOn Set.univ) (hind : IndepFun Ψ S μ)
    (g : σT × τT → (Fin k → Bool)) (hg : Measurable g)
    (r : ℕ) (hr : (r : ℝ) ≤ k / 2) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hrec : ENNReal.ofReal γ ≤ μ {ω | hammingDist (Ψ ω) (g (S ω, T ω)) ≤ r}) :
    ENNReal.ofReal (γ * k * (1 - h2 ((r : ℝ) / k)) - 1) ≤ condMutualInfoBits Ψ T S μ := by sorry

end SpatialHalfspace.FullLabels
