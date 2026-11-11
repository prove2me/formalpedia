-- Prove2me | Theorems.Thm_SepMeasures_lemma_2_3
-- name    : SepMeasures.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:05.249022+00:00
-- url     : https://prove2.me/theorems/eeb64bfb-6012-407c-9cc8-1b4507c919ac
-- title:
--   Lemma 2.3 — signed ham-sandwich theorem in $\mathbb R^d$ ([Mat03], [AK13, Thm 2.2])
-- statement:
--   Let $\lambda_1,\dots,\lambda_n$ be compactly supported finite signed measures on $\mathbb R^d$, absolutely continuous with respect to Lebesgue measure, where $n\le d$. If $\lambda_1$ is a non-zero positive measure, then some affine hyperplane $H$ simultaneously bisects $\lambda_1,\dots,\lambda_n$:
--   $$\lambda_i(H^+)=\lambda_i(H^-)\qquad(i=1,\dots,n).$$
--
--   The paper quotes this theorem from the literature; it is how the hyperplanes of Theorems 3.2 and 3.3 are chosen (applied to measures such as $\mu$, $\nu$, $\sigma_{H_1}\nu$, $\sigma_{H_1}\mu$).
--
--   **Formalization Note** "Absolutely continuous" is with respect to Lebesgue measure on `EuclideanSpace ℝ (Fin d)`; "compactly supported" means vanishing on every measurable set outside some compact set.
--
--   Differences from the source:
--   - encoding: compactly supported, absolutely continuous finite signed measures λ₁, …, λₙ; λ₁ a non-zero positive measure → s : Fin n → SignedMeasure (E d) with s i ≪ᵥ volume, a compact K_i such that every measurable subset of K_iᶜ is s i-null, 0 ≤ s 0 A for measurable A, and s 0 ≠ 0; 0 < n; reason: SignedMeasure is finite by construction; indexing from 0 makes λ₁ = s 0, which exists in the source (n ≥ 1)
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 2.3, p.13 (citing [Mat03, Chapter 3] and [AK13, Theorem 2.2])

import Mathlib
import Definitions.Def_SepMeasures_Bisects

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 2.3, p.13 (signed ham-sandwich theorem in `ℝ^d`;
[Mat03, Chapter 3], [AK13, Theorem 2.2]): let `λ₁, …, λₙ` be compactly supported, absolutely
continuous finite signed measures on `ℝ^d`, where `n ≤ d`. If `λ₁` is a non-zero positive
measure, then some affine hyperplane simultaneously bisects `λ₁, …, λₙ`.

**Formalization Note.** The measures are `s : Fin n → SignedMeasure (ℝ^d)` (finite by
construction), indexed from `0`, so `λ₁` is `s 0` (which needs `0 < n`). "Absolutely
continuous" is with respect to Lebesgue measure (`≪ᵥ volume`). "Compactly supported" is: there
is a compact `K` such that every measurable subset of `Kᶜ` has measure `0`. "Positive" is
`0 ≤ λ₁(A)` for every measurable `A`. -/
theorem lemma_2_3 (d n : ℕ) (hnd : n ≤ d) (hn : 0 < n) (s : Fin n → SignedMeasure (E d))
    (hac : ∀ i, s i ≪ᵥ (volume : Measure (E d)).toENNRealVectorMeasure)
    (hcpt : ∀ i, ∃ K : Set (E d), IsCompact K ∧ ∀ A, MeasurableSet A → A ⊆ Kᶜ → s i A = 0)
    (hpos : ∀ A, MeasurableSet A → 0 ≤ s ⟨0, hn⟩ A) (hne : s ⟨0, hn⟩ ≠ 0) :
    ∃ H : Hyp d, ∀ i, Bisects (s i) H := by sorry

end SepMeasures
