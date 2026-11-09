-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_query_representation
-- name    : WeightedSpectralSketch.LowerBound.query_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:06.103228+00:00
-- url     : https://prove2.me/theorems/a81663e0-f885-485a-8394-1b032f1cffd9
-- title:
--   Lemma 5.2 — representation of the query column of an incidence sketch
-- statement:
--   Let $t\ge1$, let $\ell\ge10$ be even and $b=(10^8+1)t+1$ (so $s=10^8t$ in the slot layout $b=t+s+1$). Fix a vertex set $R$ with $|R|=\ell b$ and an incidence sketch matrix $B=[b_e:e\in\binom R2]$ of dimension $N\le10^{-9}\ell bt$. Under the uniform random labeling of the ring slots there is an event $E$ with $\Pr\{E\}\ge0.999$ on which the query column admits a representation
--
--   $$
--   b_q=\sum_{e\in\binom R2\setminus\{q\}}f_eb_e .
--   $$
--
--   The coefficient vector $f=(f_e)_{e\ne q}$ depends only on the labeling and is zero outside $E$; $f_e=0$ whenever $b_e=0$; $\|f\|_2^2\le2\ell b$; and
--
--   $$
--   \mathbb E\Big[\sum_{0\le i<j<\ell}L(i,j)^8\sum_{\substack{u\in B_i,\,v\in B_j\\ uv\ne q}}f_{uv}^2\ \Big|\ E\Big]\le25\ell. \tag{5}
--   $$
--
--   The two coefficient bounds match the two kinds of base weights: $\|f\|_2^2$ controls the within-block edges, and the distance-weighted sum controls the cross-block edges, whose inverse squared weights carry $L(i,j)^8$.
--
--   **Formalization Note.** The query endpoints occupy the spare slots of blocks $0$ and $\ell/2$. The sum in (5) runs over the edges $\ne q$ whose endpoints lie in different blocks, each counted once.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
--   - encoding: f = (f_e) indexed by binom(R,2) \ {q}, chosen as a function of the labeling → a function of the labeling with values on the edge slots different from q; reason: the same data
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 14, Lemma 5.2, Eq. (5), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Ring
import Definitions.Def_WeightedSpectralSketch_LowerBound_Reserve

open Matrix

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 5.2, p. 14: let `t ≥ 1`, `ℓ ≥ 10` even, `b = (10⁸ + 1) t + 1`, `|R| = ℓ b`, and `B` an
incidence sketch matrix of dimension `N ≤ 10⁻⁹ ℓ b t`. Under the uniform ring labeling there is an
event `E` with `Pr{E} ≥ 0.999` and coefficients `f = (f_e)_{e ≠ q}`, determined by the labeling and
zero outside `E`, such that on `E`, `b_q = ∑_{e ≠ q} f_e b_e`; moreover `f_e = 0` whenever `b_e = 0`,
`‖f‖₂² ≤ 2 ℓ b`, and (5): `E[∑_{0 ≤ i < j < ℓ} L(i,j)⁸ ∑_{u ∈ B_i, v ∈ B_j, uv ≠ q} f_{uv}² | E] ≤ 25 ℓ`. -/
theorem query_representation {ℓ t : ℕ} [NeZero ℓ] (hℓ : 10 ≤ ℓ) (hℓe : Even ℓ) (ht : 0 < t)
    {R : Type*} [Fintype R] [DecidableEq R] (hR : Fintype.card R = ℓ * (t + 10 ^ 8 * t + 1))
    {N : ℕ} (B : Matrix (Fin N) (EdgeSlot R) ℝ) (hB : IsIncidence B)
    (hN : (N : ℝ) ≤ (ℓ : ℝ) * (t + 10 ^ 8 * t + 1 : ℕ) * t / 10 ^ 9) :
    ∃ (E : (Fin ℓ × Fin (t + 10 ^ 8 * t + 1) ≃ R) → Prop)
      (f : ∀ σ : Fin ℓ × Fin (t + 10 ^ 8 * t + 1) ≃ R, {e : EdgeSlot R // e.1 ≠ querySym σ} → ℝ),
      999 / 1000 ≤ prob E ∧
      (∀ σ, ¬ E σ → ∀ e, f σ e = 0) ∧
      (∀ σ, E σ → colS B (querySym σ) = ∑ e, f σ e • Bᵀ e.1) ∧
      (∀ σ e, Bᵀ e.1 = 0 → f σ e = 0) ∧
      (∀ σ, ∑ e, f σ e ^ 2 ≤ 2 * (ℓ : ℝ) * (t + 10 ^ 8 * t + 1 : ℕ)) ∧
      condAvg E (fun σ => ∑ e : {e : EdgeSlot R // e.1 ≠ querySym σ}, if (e.1.1.map (blockOf σ)).IsDiag then 0 else
        ((symDist ℓ (e.1.1.map (blockOf σ)) : ℝ) ^ 8 * f σ e ^ 2)) ≤ 25 * ℓ := by sorry

end WeightedSpectralSketch.LowerBound
