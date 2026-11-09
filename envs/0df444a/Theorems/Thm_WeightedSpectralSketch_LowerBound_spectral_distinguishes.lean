-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_spectral_distinguishes
-- name    : WeightedSpectralSketch.LowerBound.spectral_distinguishes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:06:51.109675+00:00
-- url     : https://prove2.me/theorems/e65a51ad-0902-44f7-8e91-144119467acf
-- title:
--   Lemma 4.2 — a spectral approximation distinguishes Yes from No
-- statement:
--   Let $b\ge1$, $\ell\ge2$ even and $|R|=\ell b$, and consider the unanchored Yes/No distributions of §4.1 (base weights (3) with $w_{\mathrm{int}}=(\ell b)^2$, noise of density (4), query edge $q$). Suppose a randomized linear sketch computes a $(1\pm0.01)$-spectral sparsifier with probability at least $0.99$ on every input in the support of No or Yes. Then there is a test which, given the recovery output $\widehat L$ and the labeling $\pi$, answers Yes or No, and which identifies the case with success probability at least $0.99$ under either distribution:
--
--   $$
--   \Pr\big[T(\pi,\widehat L)=\text{Yes}\mid\text{Yes}\big]\ge 0.99,\qquad \Pr\big[T(\pi,\widehat L)=\text{No}\mid\text{No}\big]\ge0.99,
--   $$
--
--   where the probability is over the labeling, the noise and the sketch's randomness.
--
--   This is the spectral half of the reduction: a sparsifier detects the unit increase on the query edge through a potential that varies slowly around the block cycle.
--
--   **Formalization Note.** The test is required to be measurable in $\widehat L$ for each labeling, so the probabilities are well defined.
--
--   Differences from the source:
--
--   - encoding: uniformly random permutation π placing vertices in the fixed slots → uniform distribution on bijections from the slot type to the vertex type; probabilities and conditional expectations are counting ratios; reason: a uniform permutation of [n] composed with a fixed slot numbering is a uniform bijection; same events and values
--   - encoding: a random sketch matrix independent of the input, and a recovery algorithm using A, Aw and internal randomness → one seed ω of an arbitrary probability space determines a measurable A(ω) and a jointly measurable recovery D(ω, ·); reason: the standing measurability convention of a probability experiment; independent recovery randomness is the special case of a product seed
--   - encoding: every input in the support of the Yes or No distribution → every input w̃ = w z (+ 1_q in Yes) for some labeling and noise values z_e ∈ [1/2, 3/2]; reason: [1/2, 3/2] is the closed support of density (4)
--   - encoding: one can identify whether the input was sampled from Yes or No → there exists a test T(π, L̂) ∈ {Yes, No}, measurable in L̂, with success probability ≥ 0.99 under each case; reason: the source's distinguisher is such a test
--   - encoding: vertex set R := [n], n = ℓb, with distinguished query slots fixed arbitrarily in blocks 0 and ℓ/2 → any finite vertex type of cardinality ℓb and arbitrary fixed positions j_x, j_y in blocks 0 and ℓ/2; reason: §4.1 fixes the distinguished slots arbitrarily; relabelling vertices changes nothing
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 10, Lemma 4.2 (setting §4.1, pp. 9–10), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Graph
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
import Definitions.Def_WeightedSpectralSketch_LowerBound_Ring

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 4.2, p. 10: on the unanchored ring (`|R| = ℓ b`, `b ≥ 1`, `ℓ ≥ 2` even), if a linear sketch
computes a `(1 ± 0.01)`-spectral sparsifier with probability at least `0.99` on every input in the
support of No or Yes, then a test that sees the recovery output `L̂` and the permutation `π`
identifies whether the input was sampled from Yes or No with success probability at least `0.99`
under either distribution. -/
theorem spectral_distinguishes {ℓ b : ℕ} [NeZero ℓ] (hb : 1 ≤ b) (hℓ : 2 ≤ ℓ) (hℓe : Even ℓ)
    {R : Type*} [Fintype R] [DecidableEq R] (hR : Fintype.card R = ℓ * b) (jx jy : Fin b)
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : LinearSketch R N Ω)
    (hS : ∀ w ∈ ringSupport ℓ b R jx jy, (99 / 100 : ℝ≥0∞) ≤ successProb P S (1 / 100) w) :
    ∃ T : (Fin ℓ × Fin b ≃ R) → (R → R → ℝ) → Bool, (∀ σ, Measurable (T σ)) ∧
      ∀ yes : Bool, (99 / 100 : ℝ≥0∞) ≤ ringTestSuccess ℓ b jx jy P S T yes := by sorry

end WeightedSpectralSketch.LowerBound
