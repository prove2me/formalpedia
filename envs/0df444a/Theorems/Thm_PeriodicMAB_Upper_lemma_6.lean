-- Prove2me | Theorems.Thm_PeriodicMAB_Upper_lemma_6
-- name    : PeriodicMAB.Upper.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:52.334019+00:00
-- url     : https://prove2.me/theorems/560d0874-5457-4ad8-9d31-4266f16b2532
-- title:
--   Lemma 6, p. 19 — $P(\sup_{v\in\mathcal U_k}|\tilde\epsilon_k(v)|>\delta)\le200n e^{-0.2328n\delta^2/\sigma^2}+200n e^{-0.291n\delta^2/\sigma^2}$
-- statement:
--   Let the noise satisfy Assumption 2 with parameter $\sigma>0$, let $g\ge\max\{2,\sqrt n\}$ be an integer with $T_k<n/(2g)$, and let $\mathcal U_k=[0,1/2]\cap\bigcup_{j=1}^{\lfloor T_k/2\rfloor}[j/T_k-g/n,\ j/T_k+g/n]$ be the union of the neighbourhoods of all possible nonzero present frequencies. For every $\delta>0$,
--   $$
--   \mathbb P\Big(\sup_{v\in\mathcal U_k}|\tilde\epsilon_k(v)|>\delta\Big)\le200n\exp\Big(-\frac{0.2328\,n\delta^2}{\sigma^2}\Big)+200n\exp\Big(-\frac{0.291\,n\delta^2}{\sigma^2}\Big).
--   $$
--
--   Restricting to $\mathcal U_k$ yields a sharper bound than Lemma 1, which Lemma 7 needs to locate the maxima of the periodogram within $1/n$ of the present frequencies.
--
--   **Formalization Note** The paper prints $0.233$ in the first exponent. Its proof chooses $w_1=0.965$, which gives $w_1^2/4=0.23280625$, so the statement uses $0.2328$, the largest four-decimal value the proof supports. The second exponent's unrounded value in the proof is $0.291106$. The index range $j=1,\dots,\lfloor T_k/2\rfloor$ of $\mathcal U_k$ (printed garbled on p. 19) is the one of the proof (p. 37).
-- source:
--   Chen, Wang and Wang, Learning and Optimization with Seasonal Patterns, arXiv:2005.08088v4, p. 19, Lemma 6 (index range of U_k from its proof, p. 37)

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace PeriodicMAB.Upper

/-- Lemma 6 (p. 19), with the constant `0.2328` that the proof establishes in place of the
printed `0.233`: `P(sup_{v ∈ 𝒰_k} |ε̃_k(v)| > δ) ≤ 200n exp(−0.2328 nδ²/σ²) + 200n exp(−0.291 nδ²/σ²)`. -/
theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ) (hε : IsSubGaussianNoise P ε σ)
    (p n g k : ℕ) (hA3 : Assumption3Arm n g p) (δ : ℝ) (hδ : 0 < δ) :
    P {ω | ∃ v ∈ nbhdU p n g, δ < ‖epsTilde ε n k v ω‖} ≤
      ENNReal.ofReal (200 * n * Real.exp (-(0.2328 * n * δ ^ 2 / (σ : ℝ) ^ 2)) +
        200 * n * Real.exp (-(0.291 * n * δ ^ 2 / (σ : ℝ) ^ 2))) := by sorry

end PeriodicMAB.Upper
