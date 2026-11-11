-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_8
-- name    : RamseyLST.Main.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:09:16.452379+00:00
-- url     : https://prove2.me/theorems/e3060398-39ad-4420-90c3-b2d3110ab687
-- title:
--   Lemma 8 — the candidate core: $|Z| \ge |X|^{1-1/t}$ embedding into $\mathrm{comp}_\beta((\beta t)^{O(t)})$ with distortion $1+2/\beta$
-- statement:
--   There is an absolute constant $c$ such that the following holds. Let $(X,d)$ be a finite metric space, $t>1$ and $\beta\ge2$. Then there are a subset $Z\subseteq X$ with
--
--   $$|Z|\ \ge\ |X|^{1-1/t}$$
--
--   and a non-contractive embedding $f:Z\to H$ into a space $H\in\mathrm{comp}_\beta\big((\beta t)^{ct}\big)$ with distortion at most $1+2/\beta$.
--
--   The subset $Z$ is the candidate core of the reduction (Corollary 10, applied to $(A,d_G)$). Its embedding into a metric composition with bounded aspect ratio lets the reduction recurse on the composition.
--
--   Differences from the source:
--   - encoding: comp_β((βt)^{O(t)}) → comp_β((βt)^{c t}) for one constant c chosen before X, t and β; reason: explicit constant for O(·); comp_β(Φ) grows with Φ and βt > 1, so an exponent O(t) is the same as an exponent at most c t
--   - reading: a metric space (X, d) → a finite metric space (Fintype P, IsMetric d); reason: |X|^{1−1/t} is a number only for finite X; the lemma is applied to (A, d_G) with A finite
--   - encoding: H ∈ comp_β(Φ) → a representation H : CompRep β Φ and its realised distance, together with IsMetric on that distance; reason: Definition 5 requires a fixed representation, and the conclusion requires a metric target on all its points; non-contractivity alone controls only the image
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 14 (PDF 18), Lemma 8

import Mathlib
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_MetricComposition

namespace RamseyLST.Main

/-- Lemma 8 (p. 14): there is an absolute constant `c` such that for every finite metric space
`(X, d)` and all `t > 1`, `β ≥ 2` there are `Z ⊆ X` with `|Z| ≥ |X|^{1 − 1/t}` and a
non-contractive embedding of `Z` with distortion at most `1 + 2/β` into a space of
`comp_β((βt)^{c t})`. -/
theorem lemma_8 :
    ∃ c : ℝ, ∀ (P : Type) [Fintype P] (d : P → P → ℝ), IsMetric d → ∀ t β : ℝ, 1 < t → 2 ≤ β →
      ∃ Z : Finset P, (Fintype.card P : ℝ) ^ (1 - 1 / t) ≤ (Z.card : ℝ) ∧
        ∃ (H : CompRep β ((β * t) ^ (c * t))) (f : Z → H.carrier),
          IsMetric H.dist ∧
            IsEmbeddingWithDistortion (fun a b : Z => d a b) H.dist f (1 + 2 / β) := by sorry

end RamseyLST.Main
