-- Prove2me | Theorems.Thm_SpectralFeedback_schur_concave_of_symmetric_concave
-- name    : SpectralFeedback.schur_concave_of_symmetric_concave
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:05.377093+00:00
-- url     : https://prove2.me/theorems/077bb2ba-48e3-4d61-afa9-77213d80c880
-- title:
--   Symmetric concave $F$ is Schur-concave: $x\prec y\Rightarrow F(y)\le F(x)$
-- statement:
--   Let $s\ge1$ and let $F:\mathbb R^s_+\to\mathbb R$ be symmetric and concave. If $y\in\mathbb R^s_+$ and $x\prec y$, then
--
--   $$
--   F(y)\le F(x).
--   $$
--
--   In the proof of Theorem H.2 it is applied to $c/2\prec x_{[s]}$ (Lemma F.3), giving $F(x_{[s]})\le F(c/2)$ for the balanced atom spectrum $x$.
--
--   **Formalization Note** $F$ is a function on $\mathbb R^s$ whose symmetry and concavity are assumed on the orthant only. Majorization is the published `RetailVariety.Fashion.Majorized`. No continuity or monotonicity is assumed.
--
--   Differences from the source:
--   - encoding: $F$ symmetric and concave on $\mathbb R^s_+$; Schur-concavity for vectors in $\mathbb R^s_+$ → symmetry and `ConcaveOn` on `orthant s`; hypotheses `y ∈ orthant s` and `Majorized x y`, with no hypothesis `x ∈ orthant s`; reason: $x\prec y$ with $y\ge0$ puts $x$ in the convex hull of the permutations of $y$, hence in the orthant; the dropped hypothesis excludes nothing
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), proof of Theorem H.2, p.109 (PDF p.111); argument in §F.2.1, p.93 (PDF p.95)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_RetailVariety_Fashion_Majorization

namespace SpectralFeedback

/-- **Schur-concavity of symmetric concave rewards** (Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), proof of Theorem H.2, p.109
(PDF p.111): "Symmetry and concavity make `F` Schur-concave"; argument in §F.2.1,
p.93 (PDF p.95), for `χ_s`: "majorization expresses `x` as a convex combination of permutations of `y`, so
symmetry and concavity give the stated Schur inequality").

If `F : ℝ^s_+ → ℝ` is symmetric and concave, then `x ≺ y` implies `F(y) ≤ F(x)`.

**Formalization Note** `F` is a function on `ℝ^s` whose symmetry and concavity are assumed on the
orthant `ℝ^s_+` only. Only `y ∈ ℝ^s_+` is assumed: `x ≺ y` then puts `x` in the convex hull of the
permutations of `y`, hence in `ℝ^s_+`. `x ≺ y` is the published `RetailVariety.Fashion.Majorized x y`.
Continuity and monotonicity of `F` are not assumed (the step does not use them). -/
theorem schur_concave_of_symmetric_concave (s : ℕ) (hs : 1 ≤ s) (F : (Fin s → ℝ) → ℝ)
    (hsym : ∀ σ : Equiv.Perm (Fin s), ∀ x ∈ orthant s, F (x ∘ σ) = F x)
    (hconc : ConcaveOn ℝ (orthant s) F)
    (x y : Fin s → ℝ) (hy : y ∈ orthant s) (hxy : RetailVariety.Fashion.Majorized x y) :
    F y ≤ F x := by sorry

end SpectralFeedback
