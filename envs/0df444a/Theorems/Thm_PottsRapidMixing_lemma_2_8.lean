-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_2_8
-- name    : PottsRapidMixing.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:28.665996+00:00
-- url     : https://prove2.me/theorems/85dabcb8-9412-4476-9bea-5fdfa0cd2ad2
-- title:
--   Lemma 2.8, p.13 — the random-cluster dichotomy
-- statement:
--   Fix real $q\ge1$, $\Delta\ge3$ and $0<p<p_u$. There are constants $\alpha,C>0$ and a sequence $\varepsilon_n\to0$ such that with probability $1-o(1)$ a random $\Delta$-regular graph on $n$ vertices is such that all its cycles of length at most $\ell=\alpha\log n$ are pairwise vertex disjoint, and for every distribution $\nu$ on edge configurations $A\in\{0,1\}^E$,
--   $$\mathbb E_\nu[W_{\mathrm{long}}]\le C\,I_\phi(\nu)+\varepsilon_n.\tag{2.14}$$
--
--   This is the edge version of the dichotomy, and it yields approximate tensorization of entropy for $\phi$.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - reading: constants named in a "with probability 1 − o(1)" statement → the constants are quantified before n and the graph event; reason: the stronger reading, and what the proof gives: every constant is fixed first, then G is taken in the event
--   - reading: "q ≥ 1" → q real, q ≥ 1; reason: the usual random-cluster range and the stronger reading (paper.md R4)
--   - reading: the o(1) in (2.14) → one sequence ε_n → 0, independent of G and ν, fixed before the graph event; reason: the proof gives C(n^{−ζ} + n^{−6}), (3.44) (paper.md R7)
--   - encoding: ℓ = α log n → ℓ = ⌊α log n⌋ in the conditions on cycle lengths; reason: cycle lengths are integers, so the two give the same conditions
--   - encoding: p < p_u → 0 < p < p_u; reason: 0 < β is standing; p = 1 − e^{−β}
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 2.8, (2.14), p.13

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_Cycles

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 2.8** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.13), the random-cluster dichotomy.
Fix `q ≥ 1`, `Δ ≥ 3` and `p < p_u`. There are constants `α, C > 0` such that with probability `1 − o(1)` a
random Δ-regular graph on `n` vertices is such that all its cycles of length at most `ℓ = α log n` are
pairwise vertex disjoint, while for every distribution `ν` on edge configurations,
`E_ν[W_long] ≤ C I_ϕ(ν) + o(1)`, (2.14).

**Formalization Note.** `q` is real (`q ≥ 1`, the random-cluster range). `0 < p` is the paper's `0 < β`. The
`o(1)` is one sequence `ε_n → 0` fixed before the graph event, as the proof gives (3.44). A cycle length is
an integer, so `ℓ = α log n` and `⌊α log n⌋` give the same conditions. -/
theorem lemma_2_8 (Δ : ℕ) (hΔ : 3 ≤ Δ) (q : ℝ) (hq : 1 ≤ q) (p : ℝ) (hp0 : 0 < p)
    (hpu : p < pU q Δ) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ WithHighProb Δ (fun n G =>
      ShortCyclesDisjoint G ⌊α * Real.log (n : ℝ)⌋₊ ∧
      ∀ ν : (G.edgeSet → Bool) → ℝ, MarkovMixing.IsDist ν →
        ∑ A, ν A * Wlong G ⌊α * Real.log (n : ℝ)⌋₊ A
          ≤ C * localEntropy (rcLaw G p q) ν + ε n) := by sorry

end PottsRapidMixing
