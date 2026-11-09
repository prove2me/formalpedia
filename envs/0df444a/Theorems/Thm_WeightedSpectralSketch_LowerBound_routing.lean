-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_routing
-- name    : WeightedSpectralSketch.LowerBound.routing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:11.764167+00:00
-- url     : https://prove2.me/theorems/3953c908-c908-4c6d-816b-0f07bc65823b
-- title:
--   Lemma 5.5 — routing with bounded expected cost
-- statement:
--   Let $t\ge1$, $s=10^8t$, $b=t+s+1$, and let $\ell\ge10$ be even. Fix $R$ with $|R|=\ell b$ and an incidence sketch matrix $B=[b_e:e\in\binom R2]$ of dimension $N\le10^{-9}\ell bt$. Under the uniform ring labeling there is an event $E$ with $\Pr\{E\}\ge0.999$ on which one can choose an increasing path
--
--   $$
--   0=i_0<i_1<\dots<i_m=\ell/2
--   $$
--
--   of transitions. The path is determined by the labeling and satisfies
--
--   $$
--   \mathbb E\Big[\sum_{j=1}^mL(i_j,i_{j-1})^8\ \Big|\ E\Big]\le25\ell .
--   $$
--
--   Each transition $i\to j$ moves the root-star term from reserve $T_i$ to $T_j$ at cross-block cost at most $L(i,j)^8$ (by (9)), so the path yields the distance-weighted bound (5) of Lemma 5.2.
--
--   **Formalization Note.** A path is a list of block indices starting at $0$, ending at $\ell/2$, strictly increasing, with every consecutive pair a transition in the sense of the event $E_1$ of p. 16.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
--   - encoding: an increasing path 0 = i_0 < ⋯ < i_m = ℓ/2 determined by the labeling → a function from labelings to lists of block indices satisfying the path conditions on E; reason: the same data
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 17, Lemma 5.5 (transitions defined p. 17 via E_1 p. 16), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Reserve

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 5.5, p. 17 (routing with bounded expected cost): let `t ≥ 1`, `s = 10⁸ t`,
`b = t + s + 1 = (10⁸ + 1) t + 1`, `ℓ ≥ 10` even, `|R| = ℓ b`, and `B` an incidence sketch matrix of
dimension `N ≤ 10⁻⁹ ℓ b t`. Under the uniform ring labeling there is an event `E` with
`Pr{E} ≥ 0.999` and a labeling-determined increasing path `0 = i₀ < ⋯ < i_m = ℓ/2` of transitions
on `E` with `E[∑_{j=1}^m L(i_j, i_{j-1})⁸ | E] ≤ 25 ℓ`. -/
theorem routing {ℓ t : ℕ} [NeZero ℓ] (hℓ : 10 ≤ ℓ) (hℓe : Even ℓ) (ht : 0 < t)
    {R : Type*} [Fintype R] [DecidableEq R] (hR : Fintype.card R = ℓ * (t + 10 ^ 8 * t + 1))
    {N : ℕ} (B : Matrix (Fin N) (EdgeSlot R) ℝ) (hB : IsIncidence B)
    (hN : (N : ℝ) ≤ (ℓ : ℝ) * (t + 10 ^ 8 * t + 1 : ℕ) * t / 10 ^ 9) :
    ∃ (E : (Fin ℓ × Fin (t + 10 ^ 8 * t + 1) ≃ R) → Prop)
      (path : (Fin ℓ × Fin (t + 10 ^ 8 * t + 1) ≃ R) → List (Fin ℓ)),
      999 / 1000 ≤ prob E ∧
      (∀ σ, E σ → IsTransitionPath B σ (path σ)) ∧
      condAvg E (fun σ => (pathCost ℓ (path σ) : ℝ)) ≤ 25 * ℓ := by sorry

end WeightedSpectralSketch.LowerBound
