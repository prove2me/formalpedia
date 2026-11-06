-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_3_12
-- name    : PottsRapidMixing.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:40.66875+00:00
-- url     : https://prove2.me/theorems/fb1d1865-a5f9-418f-924d-13cb4fd5b4db
-- title:
--   Lemma 3.12, p.23 — the random-graph event
-- statement:
--   Let $\Delta\ge3$, $\delta>0$, $s,\gamma\in(0,1)$ with $ds^\gamma<1$. There are constants $\eta\in(0,1/2]$ and $\alpha,\zeta>0$, depending only on $\Delta,\delta,s,\gamma$, such that for every fixed $K_w>0$ there is a fixed integer $t_w$ for which a random $\Delta$-regular graph $G$ satisfies with probability $1-o(1)$:
--
--   1. $|E(G[U])|\le(1+\delta)|U|$ for every $U\subseteq V$ with $|U|\le\eta n$;
--   2. $|E(G[U])|-|U|+1\le t_w$ for every connected $U\subseteq V$ with $|U|\le K_w\log n$;
--   3. all simple cycles of length at most $\ell=\lfloor\alpha\log n\rfloor$ are pairwise vertex-disjoint;
--   4. writing $N_j(G)$ for the number of cycles of length $j$,
--   $$T(G):=\sum_{j=\ell+1}^{\lceil K_w\log n\rceil}j^2N_j(G)\,s^{\gamma(j-1)}\le n^{-\zeta}.\tag{3.27}$$
--
--   This event says that most tests of the exploration are good, and it controls long cycles.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) over a uniformly random Δ-regular graph on n vertices → the fraction of Δ-regular graphs on Fin n with the property tends to 1 along n with nΔ even; reason: the uniform law exists exactly for nΔ even and n > Δ; same statement
--   - generalization: δ, s, γ are the constants of (3.18), left implicit → every δ > 0, s, γ ∈ (0, 1) with d s^γ < 1, quantified first; reason: the proof uses nothing else about them (paper.md R10); the page's δ of (3.18), s ∈ (s_∞, 1/d) and γ ∈ (0, 1) satisfy these conditions, so the statement specializes to the source
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 3.12, (3.27), p.23

import Mathlib
import Definitions.Def_PottsRapidMixing_Ensemble
import Definitions.Def_PottsRapidMixing_Cycles

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 3.12** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.23). There are constants
`η ∈ (0, 1/2]` and `α, ζ > 0` such that, for every fixed `K_w > 0`, there is a fixed integer `t_w` for which a
random Δ-regular graph satisfies with probability `1 − o(1)`: (1) `|E(G[U])| ≤ (1 + δ)|U|` for every
`|U| ≤ ηn`; (2) `|E(G[U])| − |U| + 1 ≤ t_w` for every connected `U` with `|U| ≤ K_w log n`; (3) all simple
cycles of length at most `ℓ = ⌊α log n⌋` are pairwise vertex-disjoint; (4) (3.27),
`T(G) = ∑_{j=ℓ+1}^{⌈K_w log n⌉} j² N_j(G) s^{γ(j−1)} ≤ n^{−ζ}`. `η, α, ζ` depend only on `Δ, δ, s, γ`, and `t_w`
may also depend on `K_w`.

**Formalization Note.** The lemma's `δ, s, γ` are those of (3.18); it holds for every `δ > 0`, `s, γ ∈ (0, 1)`
with `d s^γ < 1`, stated here. Property 2 is written with the subtraction moved across, so no natural
subtraction occurs. -/
theorem lemma_3_12 (Δ : ℕ) (hΔ : 3 ≤ Δ) (δ s γ : ℝ) (hδ : 0 < δ) (hs0 : 0 < s) (hs1 : s < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hds : ((Δ : ℝ) - 1) * s ^ γ < 1) :
    ∃ η α ζ : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ 0 < α ∧ 0 < ζ ∧ ∀ Kw : ℝ, 0 < Kw → ∃ tw : ℕ,
      WithHighProb Δ (fun n G =>
        (∀ U : Finset (Fin n), (U.card : ℝ) ≤ η * (n : ℝ) →
          (edgesIn G U : ℝ) ≤ (1 + δ) * (U.card : ℝ)) ∧
        (∀ U : Finset (Fin n), (G.induce (U : Set (Fin n))).Connected →
          (U.card : ℝ) ≤ Kw * Real.log (n : ℝ) → edgesIn G U + 1 ≤ tw + U.card) ∧
        ShortCyclesDisjoint G ⌊α * Real.log (n : ℝ)⌋₊ ∧
        cycleSum G s γ ⌊α * Real.log (n : ℝ)⌋₊ ⌈Kw * Real.log (n : ℝ)⌉₊ ≤ (n : ℝ) ^ (-ζ)) := by sorry

end PottsRapidMixing
