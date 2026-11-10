-- Prove2me | Theorems.Thm_PrivGaussMS_lemma_A_3
-- name    : PrivGaussMS.lemma_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:37.591003+00:00
-- url     : https://prove2.me/theorems/5cf28cae-b47c-4030-82f6-dbe776550674
-- title:
--   Lemma A.3 — distribution comparisons and privacy error
-- statement:
--   Let $\varepsilon\ge0$.
--
--   1. Let $p,q$ be densities of the probability laws $P,Q$ with respect to the same measure. If $P(G^c)\le\delta$ and $p\le e^{\varepsilon}q$ almost everywhere on $G$, then $P(E)\le e^{\varepsilon}Q(E)+\delta$ for every measurable event $E$.
--   2. If $M$ is $(\varepsilon,\delta)$-private and $\mathrm{TV}(\mathcal L(M(x)),\mathcal L(\tilde M(x)))\le\tau$ for every $x$, then $\tilde M$ is $(\varepsilon,\delta+(1+e^{\varepsilon})\tau)$-private.
--   3. For a public constant $w\in[0,1]$, selecting with probability $w$ a fresh call to an $(\varepsilon,\delta_0)$-private mechanism and otherwise an arbitrary input-dependent rule gives $(\varepsilon,w\delta_0+1-w)$ privacy.
--
--   Part 3 is how the correction branch, used with input-independent probability $1-w$, enters the privacy budget.
--
--   Differences from the source:
--   - encoding: mechanisms M, M̃ and the arbitrary rule → families of probability laws indexed by the dataset; DP is IsDPM (published IsDP); reason: the output law is all DP depends on
--   - encoding: densities p, q with respect to the same measure → measurable ℝ≥0∞-valued p, q with P = ν.withDensity p, Q = ν.withDensity q probability measures; reason: definition of a density of a law
--   - encoding: ε, δ ≥ 0 → 0 ≤ ε, 0 ≤ δ, 0 ≤ δ₀; reason: the paper's DP parameter range (p.24)
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.3, p.24

import Mathlib
import Definitions.Def_PrivGaussMS_Basics
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PrivGaussMS

/-- **Lemma A.3** (Distribution comparisons and privacy error), Moayedi, Yassaee, Ebrahimi,
*Optimal Private Gaussian Multi-sampling*, STOC 2027 submission (manuscript sha256 1838c582…),
p.24.

1. If `p, q` are densities of the laws `P, Q` with respect to the same measure, `P(Gᶜ) ≤ δ` and
   `p ≤ e^ε q` almost everywhere on `G`, then `P(E) ≤ e^ε Q(E) + δ` for every event `E`.
2. If `M` is `(ε, δ)`-private and `TV(L(M(x)), L(M̃(x))) ≤ τ` for every `x`, then `M̃` is
   `(ε, δ + (1 + e^ε)τ)`-private.
3. For a public constant `w ∈ [0, 1]`, selecting with probability `w` a fresh call to an
   `(ε, δ₀)`-private mechanism and otherwise an arbitrary input-dependent rule gives
   `(ε, wδ₀ + 1 − w)` privacy.

**Formalization Note.** Mechanisms are families of output laws (`IsDPM`, the published `IsDP`);
the arbitrary rule `C` of part 3 is any family of probability laws indexed by the input, with no
privacy assumed. `TV` is the published `tvDist`. `ε ≥ 0` and `δ, δ₀ ≥ 0` as in the paper's DP
definition (p.24). -/
theorem lemma_A_3 {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {n : ℕ}
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∀ (ν : Measure Ω) (p q : Ω → ℝ≥0∞) (G : Set Ω) (δ : ℝ), 0 ≤ δ → Measurable p →
        Measurable q → MeasurableSet G → IsProbabilityMeasure (ν.withDensity p) →
        IsProbabilityMeasure (ν.withDensity q) → (ν.withDensity p).real Gᶜ ≤ δ →
        (∀ᵐ z ∂ν, z ∈ G → p z ≤ ENNReal.ofReal (Real.exp ε) * q z) →
        ∀ E : Set Ω, MeasurableSet E →
          (ν.withDensity p).real E ≤ Real.exp ε * (ν.withDensity q).real E + δ) ∧
    (∀ (M Mt : (Fin n → X) → Measure Y) (δ τ : ℝ), 0 ≤ δ → IsDPM M ε δ →
        (∀ x, IsProbabilityMeasure (Mt x)) →
        (∀ x, FoundationsRL.DECLower.tvDist (M x) (Mt x) ≤ τ) →
        IsDPM Mt ε (δ + (1 + Real.exp ε) * τ)) ∧
    (∀ (M C : (Fin n → X) → Measure Y) (w δ₀ : ℝ), 0 ≤ w → w ≤ 1 → 0 ≤ δ₀ → IsDPM M ε δ₀ →
        (∀ x, IsProbabilityMeasure (C x)) →
        IsDPM (fun x => ENNReal.ofReal w • M x + ENNReal.ofReal (1 - w) • C x) ε
          (w * δ₀ + 1 - w)) := by sorry

end PrivGaussMS
