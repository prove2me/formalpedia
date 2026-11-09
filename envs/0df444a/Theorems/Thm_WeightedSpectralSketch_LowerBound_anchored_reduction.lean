-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_anchored_reduction
-- name    : WeightedSpectralSketch.LowerBound.anchored_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:41.421871+00:00
-- url     : https://prove2.me/theorems/723143a1-333d-44f1-b2d5-99429cadac70
-- title:
--   Lemma 6.1 — anchored indistinguishability reduction
-- statement:
--   Fix $b\ge2$ and an even $\ell\ge2$, let $|V|=n=2\ell b$, and consider the anchored hard distributions of §6.1 with base weights $w$ of Eq. (12) under a uniform anchored labeling $\pi$, query edge $q$, and the columns $a_e$ of a sketch matrix $A$. Write $(A\,\mathrm{diag}(w))_{-q}$ for the matrix with columns $w_ea_e$, $e\ne q$. Suppose that for **every realization** $A$ of the sketch matrix of a randomized linear sketch,
--
--   $$
--   \mathbb E_\pi\Big[\min\big\{1,\ \mathrm{lev}_{a_q}\big((A\,\mathrm{diag}(w))_{-q}\big)\big\}\Big]<\frac1{100}. \tag{13}
--   $$
--
--   Then no recovery algorithm for this sketch outputs a $(1\pm0.01)$-spectral approximation of $L_{\tilde w}$ with probability at least $0.99$ on every input $\tilde w$ in the support of either anchored distribution.
--
--   This is the reduction used for the main theorem: it turns the dimension lower bound into an upper bound on the expected truncated weighted leverage of the query column.
--
--   **Formalization Note.** The randomized sketch is a `LinearSketch` (one seed $\omega$ for the matrix and the recovery). The hypothesis is required at every seed. The conclusion negates success with probability $\ge0.99$ (an `ℝ≥0∞` probability) on all of the support.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
--   - encoding: a random sketch matrix independent of the input, and a recovery algorithm using A, Aw and internal randomness → one seed ω of an arbitrary probability space determines a measurable A(ω) and a jointly measurable recovery D(ω, ·); reason: the standing measurability convention of a probability experiment; independent recovery randomness is the special case of a product seed
--   - encoding: every input in the support of the Yes or No distribution → every input w̃ = w z (+ 1_q in Yes) for some labeling and noise values z_e ∈ [1/2, 3/2]; reason: [1/2, 3/2] is the closed support of density (4)
--   - encoding: vertex set [n], n = 2ℓb, with the query slots of Section 4 → any finite vertex type of cardinality 2ℓb and arbitrary fixed query positions j_x, j_y in blocks 0 and ℓ/2; reason: Section 4 fixes the distinguished slots arbitrarily; relabelling vertices changes nothing
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 22, Lemma 6.1, Eq. (13), with Eq. (12) p. 21, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Leverage
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Anchor

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 6.1, p. 22: on the anchored template (`n = 2 ℓ b`, `b ≥ 2`, `ℓ ≥ 2` even), if for every
realization `A` of the sketch matrix `E_π[min{1, lev_{a_q}((A diag(w))_{-q})}] < 1/100` (13) with the
base weights (12), then no recovery algorithm for this sketch computes a `(1 ± 0.01)`-spectral
approximation with probability at least `0.99` on every input in the support of either anchored
distribution. -/
theorem anchored_reduction {ℓ b : ℕ} [NeZero ℓ] (hb : 2 ≤ b) (hℓ : 2 ≤ ℓ) (hℓe : Even ℓ)
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Fintype.card V = 2 * (ℓ * b)) (jx jy : Fin b)
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : LinearSketch V N Ω)
    (hlev : ∀ ω, avg (fun π : AnchSlot ℓ b ≃ V =>
      (min 1 (lev (fun e : {e : EdgeSlot V // e.1 ≠ anchQuery π jx jy} =>
          anchBaseWeight ℓ b π e.1 • (Matrix.of (S.A ω))ᵀ e.1)
        (colS (Matrix.of (S.A ω)) (anchQuery π jx jy)))).toReal) < 1 / 100) :
    ¬ ∀ w ∈ anchSupport ℓ b V jx jy, (99 / 100 : ℝ≥0∞) ≤ successProb P S (1 / 100) w := by sorry

end WeightedSpectralSketch.LowerBound
