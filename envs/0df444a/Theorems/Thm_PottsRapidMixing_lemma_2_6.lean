-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_2_6
-- name    : PottsRapidMixing.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:54:48.921193+00:00
-- url     : https://prove2.me/theorems/571ccb14-1821-47ee-abb5-f85b0acd70b5
-- title:
--   Lemma 2.6, p.12 — the spin shattering–escape dichotomy
-- statement:
--   Let $\Delta\ge3$, $q\ge2$ and $0<\beta<\beta_u(q,\mathbb T_\Delta)$. There are constants $C_0,C_0'>0$ such that for $L=C_0\log n$, with probability $1-o(1)$ a random $\Delta$-regular graph $G$ has the property that for every spin distribution $\nu$,
--   $$\mathbb E_{\nu,M}[W_L(H)]\le C_0'\,I_\mu(\nu)+n^{-5}.$$
--
--   Either $I_\mu(\nu)$ is large, and escape from $\nu$ is fast by Lemma 2.5, or the sprinkled edge configuration drawn from $\nu$ is shattered.
--
--   **Formalization Note** "For every $\nu$" is inside the event. $\nu$ need not have full support.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - encoding: M, the standing chain of §2 → M = M(r) with r of (2.1), rOf Δ q β; reason: §2, p.9 fixes these parameters
--   - encoding: β < β_u (or B < B_u), with β > 0 standing → 0 < β < β_u(q, T_Δ); reason: 0 < β is standing on pp.1, 9; B = e^β
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 2.6, p.12

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_ChainM

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 2.6** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.12), the spin shattering–escape
dichotomy. Suppose `β < β_u`. There are constants `C₀, C₀' > 0` such that for `L = C₀ log n`, with
probability `1 − o(1)` for a random Δ-regular graph, for every spin distribution `ν`,
`E_{ν,M}[W_L(H)] ≤ C₀' I_µ(ν) + n^{−5}`.

**Formalization Note.** `M` is the chain of (2.1), `r = rOf Δ q β`. The constants sit outside the
probability, and "for every `ν`" sits inside the event. `ν` need not have full support. -/
theorem lemma_2_6 (Δ q : ℕ) (hΔ : 3 ≤ Δ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (hβu : β < betaU (q : ℝ) Δ) :
    ∃ C₀ C₀' : ℝ, 0 < C₀ ∧ 0 < C₀' ∧ WithHighProb Δ (fun n G =>
      ∀ ν : (Fin n → Fin q) → ℝ, MarkovMixing.IsDist ν →
        ∑ H : G.edgeSet → Bool, edgeMix G β (rOf Δ (q : ℝ) β) ν H *
            WL (edgeGraph G H) (C₀ * Real.log (n : ℝ))
          ≤ C₀' * localEntropy (pottsLaw G β q) ν + (n : ℝ) ^ (-5 : ℤ)) := by sorry

end PottsRapidMixing
