-- Prove2me | Theorems.Thm_PolySampIso_lemma_31
-- name    : PolySampIso.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:11.570111+00:00
-- url     : https://prove2.me/theorems/2c5b3b14-6061-4697-81b8-1188985e63c6
-- title:
--   Lemma 31, p.44 — weak conductance gives defective variance decay
-- statement:
--   Let $K$ be a $\tfrac12$-lazy Markov kernel on a measurable space $\Omega$, reversible with respect to a probability measure $\mu$, and let $b\in(0,1]$, $\delta\in(0,\tfrac12)$. Suppose that for every measurable $B\subseteq\Omega$
--
--   $$\int_BK(z,\Omega\setminus B)\,\mu(dz)\ge b\max\{\min\{\mu(B),\mu(\Omega\setminus B)\}-\delta,\,0\}.\tag{60}$$
--
--   Then for every bounded measurable $f:\Omega\to\mathbb R$ and $N\in\mathbb N$,
--
--   $$\mathrm{Var}_\mu[K^Nf]\le\exp\Big(-\frac{b^2N}2\Big)\mathrm{Var}_\mu[f]+2\delta\,\mathrm{osc}(f)^2.$$
--
--   A conductance bound that is allowed to fail on sets of mass up to $\delta$ still gives geometric variance decay, up to an additive defect proportional to $\delta$. This is the weak Poincaré mechanism (after [ALPW26]) that turns the instancewise conductance of Algorithm 6 into Lemma 32.
--
--   Differences from the source:
--   - encoding: ½-lazy (K(x, ·) places at least half its mass on x) → K(x, ·) ≥ ½δₓ as measures; reason: equivalent to K(x, {x}) ≥ ½ when singletons are measurable; Ω is abstract here
--   - encoding: bounded f, N ∈ N, osc(f) → bounded measurable f, N ≥ 1, the µ-essential oscillation; reason: functions are measurable by the paper's standing convention; N starts at 1; osc is defined with ess sup/ess inf (p.42)
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 31, p.44 (PDF p.46)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_MarkovKernel

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Lemma 31** (weak conductance gives defective variance decay).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Lemma 31, p.44 (PDF p.46):

"Lemma 31. Let K be a 1/2-lazy Markov kernel on Ω that is reversible with respect to µ ∈ P(Ω), let
b ∈ (0, 1], and let δ ∈ (0, 1/2). If for every measurable B ⊆ Ω,
∫B K(z, Ω \ B)µ(dz) ≥ b max {min {µ(B), µ(Ω \ B)} − δ, 0} , (60)
then for every bounded f : Ω → R and N ∈ N, Varµ[KNf] ≤ exp(−b²N/2) Varµ[f] + 2δosc(f)²."

**Formalization Note.** `Ω` is an abstract measurable space. ½-lazy is `K(x, ·) ≥ ½δ_x`;
reversible is detailed balance. `K^N f` is `kapply (kpow K N) f`; `Var_µ` is `variance` (bounded
measurable `f`, so finite); `osc` is the `µ`-essential oscillation. "Bounded f" is taken
measurable (standing convention). `N ∈ N` is `N ≥ 1`. -/
theorem lemma_31 {Ω : Type*} [MeasurableSpace Ω] (K : Kernel Ω Ω) [IsMarkovKernel K]
    (hlazy : IsHalfLazy K) (μ : Measure Ω) [IsProbabilityMeasure μ] (hrev : IsReversible K μ)
    (b δ : ℝ) (hb0 : 0 < b) (hb1 : b ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (h60 : ∀ B : Set Ω, MeasurableSet B →
      ENNReal.ofReal (b * max (min (μ.real B) (μ.real Bᶜ) - δ) 0) ≤ ∫⁻ z in B, K z Bᶜ ∂μ)
    (f : Ω → ℝ) (hfm : Measurable f) (hfb : ∃ M, ∀ x, |f x| ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    variance (kapply (kpow K N) f) μ ≤
      Real.exp (-b ^ 2 * N / 2) * variance f μ + 2 * δ * osc f μ ^ 2 := by sorry

end PolySampIso
