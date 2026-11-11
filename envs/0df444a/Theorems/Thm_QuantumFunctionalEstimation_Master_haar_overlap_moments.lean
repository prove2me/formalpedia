-- Prove2me | Theorems.Thm_QuantumFunctionalEstimation_Master_haar_overlap_moments
-- name    : QuantumFunctionalEstimation.Master.haar_overlap_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:30:19.982304+00:00
-- url     : https://prove2.me/theorems/262a757a-4c02-4749-893d-2b34b0d5410c
-- title:
--   Lemma 2.4 — absolute centered Haar overlap moments
-- statement:
--   Let $D\ge1$ and let $u,v$ be independent Haar-random complex unit vectors in $\mathbb C^D$. For every integer $k\ge0$,
--   $$\mathbb E\left[\left|D|\langle u,v\rangle|^2-1\right|^k\right]\le 2^k k!.$$
--   The conclusion includes $D=1$ and $k=0$. These centered overlap moments are a quantitative input for the one-direction encoding bound.
--
--   Differences from the source:
--   - encoding: independent complex Haar unit vectors → product of two first-column Haar pushforward laws; reason: normalized Haar on U(D) induces precisely the uniform unit-vector law for every positive D
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), Lemma 2.4, printed p. 13 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Definitions.Def_QuantumFunctionalEstimation_Master_Encodings
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise

namespace QuantumFunctionalEstimation.Master

/-- Lemma 2.4, printed p.13 (PDF p.15), including D=1 and k=0. -/
theorem haar_overlap_moments (D : ℕ) (hD : 0 < D) (k : ℕ) :
    (∫ t : (Fin D → ℂ) × (Fin D → ℂ),
      |(D : ℝ) * Complex.normSq (∑ i, star (t.1 i) * t.2 i) - 1| ^ k
      ∂((haarDirection D hD).prod (haarDirection D hD))) ≤
      (2 : ℝ) ^ k * (Nat.factorial k : ℝ) := by sorry

end QuantumFunctionalEstimation.Master
