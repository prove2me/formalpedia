-- Prove2me | Theorems.Thm_PricingSamples_OneSampleMHR_lemma_G_1
-- name    : PricingSamples.OneSampleMHR.lemma_G_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:05.247357+00:00
-- url     : https://prove2.me/theorems/f3d28071-a136-47c2-8c64-2d702bdc8f72
-- title:
--   Lemma G-1, p. App-32 — beyond r_F, the revenue v·G_α(v) of the generalized Pareto interpolant is non-increasing on [w, ∞)
-- statement:
--   **Revenue of the interpolant beyond the optimal price.** Fix $\alpha \in [0,1]$, $F \in \mathcal F_\alpha$ with ccdf $\bar F$ and quantiles $q_w = \bar F(w)$, and an oracle optimal price $r_F$, i.e. a maximizer of $p \mapsto p\bar F(p)$ on $[0,\infty)$. Let $w < w'$ with $w > r_F$. Then the revenue curve of the generalized Pareto tail through $(w,q_w)$ and $(w',q_{w'})$,
--
--   $$v \;\longmapsto\; v\,\Gamma_\alpha\!\Big(\Gamma_\alpha^{-1}\big(\tfrac{q_{w'}}{q_w}\big)\frac{v-w}{w'-w}\Big),$$
--
--   is non-increasing on $[w,\infty)$.
--
--   The lemma is used in the proof of Proposition 2 ii.) (p. App-7): to the right of the optimal price, the lower envelope of Lemma 2 has a non-increasing revenue curve, which is the hypothesis of Lemma 1 ii.).
--
--   **Formalization Note** The Lean function is $v \mapsto v\,G_\alpha(v \mid (w,q_w),(w',q_{w'}))$, which is $q_w$ times the printed function; $r_F$ is any maximizer (`IsOptPrice`).
--
--   Differences from the source:
--
--   - reading: Definition 2 (pp. 11–12): F admits a density f and the virtual value φ_F(v) = v − (1 − F(v))/f(v) satisfies φ_F(v′) − φ_F(v) ≥ α(v′ − v) for all v′ ≥ v in the support S_F → μ ≪ Lebesgue measure, and v ↦ Γ_α^{−1}(F̄(v)) is convex on {v ≥ 0 : F̄(v) > 0}; reason: the paper's own equivalent form, used in the proof of Lemma 2 (p. App-10, after Schweizer–Szech); it avoids evaluating an a.e.-defined density pointwise and takes the support to be an interval, as the paper's proofs do (with a gap in the support, e.g. F̄ = e^{−v} on [0,1], e^{−1} on [1,2], e^{−(v−1)} beyond, the pointwise condition holds at α = 1 but Lemma 2 fails at w = 0, w′ = 2, v = 1.5)
--   - encoding: F in 𝓕_α (α ∈ [0, 1] implicit) → explicit hypothesis α ∈ [0, 1]; reason: 𝓕_α is defined only for α ∈ [0, 1] (Definition 2)
--   - reading: r_F := arg max_{p≥0} p F̄(p), presumed unique (p. 12) → any r ≥ 0 maximizing p ↦ p F̄(p) over [0, ∞); reason: the maximizer is unique for α > 0, so this is r_F; for α = 0 the printed arg max may be a set and the statement is applied to each of its elements
--   - encoding: the function v ↦ v Γ_α(Γ_α^{−1}(q_{w′}/q_w)(v − w)/(w′ − w)) → v ↦ v · G_α(v | (w, q_w), (w′, q_{w′})), i.e. q_w times the printed function; reason: multiplying by the constant q_w > 0 does not change monotonicity; when q_w = 0 the printed q_{w′}/q_w is 0/0 and the Lean function is identically 0; the q_{w′} = 0 conventions of p. 16 are encoded in G_α
--   - encoding: a cdf F on [0, ∞) with 0 < E_F[v] < ∞ (class G, p. 11), F̄ = 1 − F → a probability measure μ on ℝ with μ((−∞, 0)) = 0, v ↦ v integrable, 0 < ∫ v dμ; F̄(p) = μ((p, ∞)); reason: same objects; F̄(p) = 1 − F(p) = P(v > p) is the strict tail
-- source:
--   Allouah, Bahamou, Besbes, Pricing with Samples, SSRN 3334650 (rev. 06/02/2021), p. App-32 (PDF p. 64), Lemma G-1

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

namespace PricingSamples.OneSampleMHR

open MeasureTheory

/-- Lemma G-1 (p. App-32): for `F ∈ 𝓕_α`, `w < w′` and `w` above an oracle optimal price `r_F`,
the revenue `v ↦ v · G_α(v | (w, q_w), (w′, q_{w′}))` of the two-point generalized Pareto
interpolant is non-increasing on `[w, ∞)`. (`G_α(v | …) = q_w Γ_α(Γ_α^{−1}(q_{w′}/q_w)(v − w)/(w′ − w))`
is `q_w` times the paper's function, a positive factor when `q_w > 0`.) -/
theorem lemma_G_1 (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) (hF : InFAlpha α μ)
    (r : ℝ) (hr : IsOptPrice μ r) (w w' : ℝ) (hww' : w < w') (hrw : r < w) :
    AntitoneOn (fun v => v * Galpha α w (ccdf μ w) w' (ccdf μ w') v) (Set.Ici w) := by sorry

end PricingSamples.OneSampleMHR
