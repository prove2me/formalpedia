-- Prove2me | Theorems.Thm_SpatialHalfspace_FullLabels_lemma_B_3
-- name    : SpatialHalfspace.FullLabels.lemma_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:29:04.794961+00:00
-- url     : https://prove2.me/theorems/90062cb6-170d-45cd-ba1f-e8a211691e68
-- title:
--   Lemma B.3 — Local estimation
-- statement:
--   Let $\mu=(\mu_u)_{u\in U}$ be feature marginals on $\mathbb R^D$, $K\ge 1$ and $\tau,\delta\in(0,1)$. Suppose at most $K$ conditional label probabilities $\eta_{u,x}$ must be reported, with $\mu_u(\{x\})\ge m_*>0$ for each required pair $(u,x)$. Let
--
--   $$L_0=\ln(4K/\delta),\qquad M=\Big\lceil\frac{2L_0}{\tau^2}\Big\rceil,\qquad N=\Big\lceil\frac{8(M+L_0)}{m_*}\Big\rceil.\tag{30}$$
--
--   From $N$ samples per terminal, the required probabilities can be estimated and reported so that, with probability at least $1-\delta$, every reported estimate differs from its conditional label probability by at most $\tau$, for every $P\in\mathcal E(\mu)$. Each report uses $\lceil\log_2(\lceil 2/\tau\rceil+1)\rceil$ bits on every execution.
--
--   **Formalization Note** The reports are measurable functions of the $N$ examples of the corresponding terminal alone, chosen without knowledge of $P$; each report is a string of exactly $\lceil\log_2(\lceil 2/\tau\rceil+1)\rceil$ bits (`Nat.clog 2`), and a fixed decoding map turns it into the reported estimate. The examples are i.i.d. from $P_u$ at each terminal, independently across terminals.
--
--   Differences from the source:
--
--   - reading: the required probabilities can be estimated and reported → there exist report maps, one per required pair, each a measurable function of that terminal’s N examples only and independent of P, and a decoding map, with the success event of probability ≥ 1 − δ for every P ∈ E(μ); reason: the terminals do not know P; the estimator of the proof is of this form
--   - encoding: ⌈log₂(⌈2/τ⌉+1)⌉ bits on every execution → reports of type Fin (Nat.clog 2 (⌈2/τ⌉₊ + 1)) → Bool; reason: Nat.clog 2 m = ⌈log₂ m⌉ for m ≥ 1; a fixed-length string uses that many bits on every execution
--   - generalization: a positive feature dimension and a terminal population with required reports → any natural feature dimension, finite terminal set and at most K required reports, including zero reports or empty terminals; reason: with no required pairs the accuracy event is universal; dimension zero still permits the same atomwise Bernoulli estimator; positive-dimensional nonempty source instances are included
--   - generalization: probability feature marginals μ_u → arbitrary measures μ_u, with the estimation guarantee required for every P ∈ E(μ); reason: if any μ_u is not a probability measure then E(μ) is empty and constant reports suffice; every source marginal tuple is included
-- source:
--   Yang, Spatial Communication Complexity of Agnostic Halfspace Learning, STOC 2027 submission #119 (2026), preprint, SHA-256 e5822ae144143c29214b0dab09b1a1863f55740d17b6f50ed091ddf8ffcaa692, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/119.pdf, printed p. 16, PDF p. 17, Lemma B.3, eq. (30), PDF pp. 17–18

import Definitions.Def_SpatialHalfspace_FullLabels_Construction

open MeasureTheory ProbabilityTheory UnderstandingML
open scoped ENNReal InnerProductSpace

namespace SpatialHalfspace.FullLabels

/-- Lemma B.3 (Local estimation), printed p. 16. For `K ≥ 1`, `τ, δ ∈ (0,1)`, at most `K`
required pairs `(u, x)` with `μ_u({x}) ≥ m_* > 0`, and `L₀ = ln(4K/δ)`, `M = ⌈2L₀/τ²⌉`,
`N = ⌈8(M + L₀)/m_*⌉`: from `N` samples per terminal, each required `η_{u,x}` can be estimated and
reported (a function of terminal `u`'s samples only, chosen without knowing `P`) so that for every
`P ∈ E(μ)`, with probability at least `1 − δ` every reported estimate is within `τ` of
`η_{u,x}`; each report is a string of exactly `⌈log₂(⌈2/τ⌉ + 1)⌉` bits. -/
theorem lemma_B_3 {D : ℕ} {U : Type} [Fintype U] (μ : U → Measure (Vec D)) (K : ℕ) (hK : 1 ≤ K)
    (τ δ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (req : Finset (U × Vec D)) (hreq : req.card ≤ K) (mstar : ℝ) (hm : 0 < mstar)
    (hmass : ∀ ux ∈ req, ENNReal.ofReal mstar ≤ μ ux.1 {ux.2}) :
    ∃ (report : U × Vec D →
        (Fin ⌈8 * ((⌈2 * Real.log (4 * K / δ) / τ ^ 2⌉₊ : ℝ) + Real.log (4 * K / δ)) / mstar⌉₊ →
          Example D) → (Fin (Nat.clog 2 (⌈2 / τ⌉₊ + 1)) → Bool))
      (decode : (Fin (Nat.clog 2 (⌈2 / τ⌉₊ + 1)) → Bool) → ℝ),
      (∀ ux, Measurable (report ux)) ∧
      ∀ P ∈ env μ, ENNReal.ofReal (1 - δ) ≤
        (Measure.infinitePi fun u : U => Measure.infinitePi fun _ :
            Fin ⌈8 * ((⌈2 * Real.log (4 * K / δ) / τ ^ 2⌉₊ : ℝ) + Real.log (4 * K / δ)) / mstar⌉₊ =>
              P u)
          {s | ∀ ux ∈ req, |decode (report ux (s ux.1)) - condProbOne (P ux.1) ux.2| ≤ τ} := by sorry

end SpatialHalfspace.FullLabels
