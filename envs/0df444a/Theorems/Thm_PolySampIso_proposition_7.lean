-- Prove2me | Theorems.Thm_PolySampIso_proposition_7
-- name    : PolySampIso.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:31.985563+00:00
-- url     : https://prove2.me/theorems/9e67851b-80f6-4b1b-9c77-c2d844c42cd3
-- title:
--   Proposition 7, p.44 — TV overlap lower-bounds conductance ([DCWY19, Lemma 6])
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be Borel, $K$ a Markov kernel on $\Omega$ reversible with respect to a probability measure $\mu$ on $\Omega$, and $\mathcal K\subseteq\Omega$ a convex Borel set with $\mu(\mathcal K)>0$ such that $\mu(\cdot\mid\mathcal K)$ is $\alpha$-strongly log-concave ($\alpha>0$). Suppose that for some $\eta\in(0,1)$ and $\Delta>0$,
--
--   $$\mathrm{TV}(K(z,\cdot),K(w,\cdot))\le1-\eta\quad\text{for all }z,w\in\mathcal K\text{ with }\|z-w\|_2\le\Delta.$$
--
--   Then for every Borel $B\subseteq\Omega$,
--
--   $$\int_BK(z,\Omega\setminus B)\,\mu(dz)\ge\frac\eta4\min\Big\{1,\frac{\log2\cdot\Delta\,\mu(\mathcal K)^2\sqrt\alpha}{8}\Big\}\min\{\mu(B\cap\mathcal K),\mu((\Omega\setminus B)\cap\mathcal K)\}.$$
--
--   This converts a local overlap bound into a conductance bound restricted to the well-conditioned region $\mathcal K$; in Lemma 32 it is applied with $\mathcal K$ the image of $B_\tau(\gamma,\tfrac14)$ in whitened coordinates.
--
--   Differences from the source:
--   - encoding: a Markov kernel on Ω and µ ∈ P(Ω) → a Markov kernel on ℝⁿ with K(z, Ωᶜ) = 0 for z ∈ Ω, and a probability measure µ on ℝⁿ with µ(Ωᶜ) = 0; reason: a kernel on Ω extends to ℝⁿ; values off Ω are not used
--   - encoding: reversible with respect to µ → detailed balance ∫_A K(·, B) dµ = ∫_B K(·, A) dµ for all measurable A, B; reason: the definition of reversibility
--   - reading: µ(· | 𝒦) is α-strongly log-concave → µ(· | 𝒦) has Lebesgue density e^{−U} on 𝒦 with U − (α/2)‖·‖² convex on 𝒦, α > 0; reason: the standard meaning in [DCWY19]: a density proportional to e^{−U} with U α-strongly convex
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 7, p.44 (PDF p.46), citing [DCWY19, Lemma 6]

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_PolySampIso_MarkovKernel
import Definitions.Def_PolySampIso_LogConcave

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Proposition 7** (TV overlap lower-bounds conductance, [DCWY19, Lemma 6]).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Proposition 7, p.44 (PDF p.46):

"Proposition 7 (Lemma 6, [DCWY19]). Let Ω be a Borel subset of Rn, and let 𝖪 be a Markov kernel on Ω
reversible with respect to µ ∈ P(Ω). Let 𝒦 ⊆ Ω be convex and Borel with µ(𝒦) > 0, and suppose that
µ(· | 𝒦) is α-strongly log-concave. If for some (η, ∆) ∈ (0, 1) × R>0, we have
TV(𝖪(z, ·), 𝖪(w, ·)) ≤ 1 − η for all z, w ∈ 𝒦 with ∥z − w∥2 ≤ ∆, then for any Borel B ⊆ Ω,
∫B 𝖪(z, Ω \ B)µ(dz) ≥ (η/4) min{1, log 2 · ∆µ(𝒦)²√α/8} min {µ(B ∩ 𝒦), µ((Ω \ B) ∩ 𝒦)} ."

**Formalization Note.** The kernel `K` (the paper's sans-serif 𝖪) is a Markov kernel on `ℝⁿ` that
maps `Ω` into `Ω`; `µ ∈ P(Ω)` is a probability measure on `ℝⁿ` with `µ(Ωᶜ) = 0`; reversibility is
detailed balance. The convex set is `S` (the paper's calligraphic 𝒦). "µ(· | 𝒦) is α-strongly
log-concave" is `IsStronglyLogConcaveOn (µ[|S]) S α`: a Lebesgue density `e^{−U}` on `S` with
`U − (α/2)‖·‖²` convex; `α > 0`. -/
theorem proposition_7 {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : MeasurableSet Ω)
    (K : Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) [IsMarkovKernel K]
    (hKΩ : ∀ z ∈ Ω, K z Ωᶜ = 0)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ] (hμΩ : μ Ωᶜ = 0)
    (hrev : IsReversible K μ)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSΩ : S ⊆ Ω) (hSc : Convex ℝ S)
    (hSm : MeasurableSet S) (hSpos : 0 < μ S)
    (α : ℝ) (hα : 0 < α) (hslc : IsStronglyLogConcaveOn (ProbabilityTheory.cond μ S) S α)
    (η Δ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hΔ : 0 < Δ)
    (hTV : ∀ z ∈ S, ∀ w ∈ S, ‖z - w‖ ≤ Δ → tvDist (K z) (K w) ≤ 1 - η)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : MeasurableSet B) (hBΩ : B ⊆ Ω) :
    ENNReal.ofReal (η / 4 * min 1 (Real.log 2 * Δ * μ.real S ^ 2 * Real.sqrt α / 8) *
        min (μ.real (B ∩ S)) (μ.real ((Ω \ B) ∩ S))) ≤
      ∫⁻ z in B, K z (Ω \ B) ∂μ := by sorry

end PolySampIso
