-- Prove2me | Theorems.Thm_WeightedSpectralSketch_LowerBound_hellinger_tensorization
-- name    : WeightedSpectralSketch.LowerBound.hellinger_tensorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:04:05.510907+00:00
-- url     : https://prove2.me/theorems/b851d080-81d0-4802-a993-644270e87a44
-- title:
--   Lemma 3.3 (tensorization clause) — Hellinger distance of products; the TV clause is FoundationsRL.DECLower.sq_tvDist_le_hellingerSq_le_klDiv
-- statement:
--   For each $i\in[m]$ let $P_i,Q_i$ be probability distributions on the same measurable space $\mathcal X_i$ (the spaces may differ with $i$). Then
--
--   $$
--   H^2\Big(\bigotimes_{i=1}^mP_i,\ \bigotimes_{i=1}^mQ_i\Big)\le\sum_{i=1}^mH^2(P_i,Q_i).
--   $$
--
--   Here $H^2(P,Q)=\tfrac12\int(\sqrt p-\sqrt q)^2\,d\mu$. Subadditivity over independent coordinates lets the Hellinger distance between the noisy Yes and No weight vectors be computed edge by edge (Lemma 4.4).
--
--   The second clause of Lemma 3.3, $\mathrm{TV}(P,Q)\le\sqrt2\,H(P,Q)$, is the first conjunct of the platform theorem `FoundationsRL.DECLower.sq_tvDist_le_hellingerSq_le_klDiv` (there $D_H^2=2H^2$), included in this mission as a reference item.
--
--   Differences from the source:
--
--   - encoding: Lemma 3.3 states the tensorization inequality and TV(P,Q) ≤ √2 H(P,Q) together → this item states the tensorization inequality; the TV clause is the companion reference item FoundationsRL.DECLower.sq_tvDist_le_hellingerSq_le_klDiv (ofReal(TV²) ≤ D²_H = 2H²); reason: the TV clause is already posed on the platform; the two items together state the whole lemma
--   - encoding: index set [m] → Fin m; reason: relabelling of the index
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 9, Lemma 3.3 (first clause), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_WeightedSpectralSketch_LowerBound_Stat

open MeasureTheory
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- Lemma 3.3, p. 9 (first clause): for probability measures `P_i, Q_i` on a measurable space
`α i`, `i ∈ [m]`, `H²(⨂ P_i, ⨂ Q_i) ≤ ∑ H²(P_i, Q_i)`. -/
theorem hellinger_tensorization {m : ℕ} {α : Fin m → Type*} [∀ i, MeasurableSpace (α i)]
    (P Q : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (P i)]
    [∀ i, IsProbabilityMeasure (Q i)] :
    hellinger2 (Measure.pi P) (Measure.pi Q) ≤ ∑ i, hellinger2 (P i) (Q i) := by sorry

end WeightedSpectralSketch.LowerBound
