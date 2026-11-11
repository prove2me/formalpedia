-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_7
-- name    : RamseyLST.Main.lemma_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:09:06.022565+00:00
-- url     : https://prove2.me/theorems/d3e3bf52-dcff-4a8f-bba0-2cb791453488
-- title:
--   Lemma 7 — a space close to an $\eta\beta$-HST is $(1+2/\beta)$-close to a space of $\mathrm{comp}_\beta(\eta)$
-- statement:
--   Let $\eta,\beta\ge1$ and let $(X,d)$ be a finite metric space. If $X$ embeds with distortion $\eta$ into an $\eta\beta$-HST (Definition 4), then $X$ embeds with distortion $1+2/\beta$ into a metric space of $\mathrm{comp}_\beta(\eta)$ (Definition 5). Here embedding with distortion $\theta$ means an injective, non-contractive map $g$ with $d_H(g(x),g(y))\le\theta\,d(x,y)$ for all $x,y$.
--
--   This is [BLMN05, Lemma 3.16]. It turns the well-separated hierarchy of Lemma 6 into a metric composition whose base spaces have aspect ratio at most $\eta$.
--
--   Differences from the source:
--   - encoding: a metric space → a finite metric space (Fintype P, IsMetric d); reason: a space that embeds injectively into a µ-HST, a finite tree, is finite; no instance is lost
--   - reading: embeds with distortion η / with distortion (1 + 2/β) → injective, non-contractive maps with ratio ≤ η, resp. ≤ 1 + 2/β (Definition 1); reason: Definition 1 defines distortion for non-contractive embeddings; µ-HSTs and comp_β(η) are closed under scaling, so this is equivalent to the scale-invariant reading
--   - encoding: a metric space from comp_β(η) → a representation R : CompRep β η and its realised distance, together with IsMetric on that distance; reason: Definition 5 requires a fixed representation, and the conclusion requires a metric target on all its points; non-contractivity alone controls only the image
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 14 (PDF 18), Lemma 7

import Mathlib
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_HST
import Definitions.Def_RamseyLST_Main_MetricComposition

namespace RamseyLST.Main

/-- Lemma 7 (p. 14, [BLMN05, Lemma 3.16]): for `η, β ≥ 1`, if a finite metric space embeds with
distortion `η` into an `ηβ`-HST, then it embeds with distortion `1 + 2/β` into a space of
`comp_β(η)`. -/
theorem lemma_7 (η β : ℝ) (hη : 1 ≤ η) (hβ : 1 ≤ β) (P : Type) [Fintype P] (d : P → P → ℝ)
    (hd : IsMetric d)
    (hemb : ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : HST Q) (f : P → Q),
      H.IsMuHST (η * β) ∧ IsEmbeddingWithDistortion d H.dist f η) :
    ∃ (R : CompRep β η) (g : P → R.carrier),
      IsMetric R.dist ∧ IsEmbeddingWithDistortion d R.dist g (1 + 2 / β) := by sorry

end RamseyLST.Main
