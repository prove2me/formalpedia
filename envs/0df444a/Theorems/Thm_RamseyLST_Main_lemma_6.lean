-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_6
-- name    : RamseyLST.Main.lemma_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:10.903331+00:00
-- url     : https://prove2.me/theorems/ffaf35b1-f2c1-47f6-b7b8-d3850dc49aa0
-- title:
--   Lemma 6 — a large subset of an HST embeds into a $\mu$-HST with distortion $\eta$
-- statement:
--   Let $\mu>\eta>1$ and let $U$ be an HST (Definition 4) on $n$ points. Then there is a subset $S$ of the points of $U$ with
--
--   $$|S|\ \ge\ n^{\,1-1/\lceil\log_{\mu/\eta}\eta\rceil}$$
--
--   which embeds with distortion $\eta$ into a $\mu$-HST: there are a $\mu$-HST $H$ and an injective, non-contractive map $f:S\to H$ with $d_H(f(x),f(y))\le\eta\,d_U(x,y)$ for all $x,y\in S$.
--
--   This is [BLMN05, Lemma 3.15]. In the construction of the candidate core it passes from the HST of Theorem 5 to a well-separated hierarchy.
--
--   Differences from the source:
--   - reading: embedded into a µ-HST with distortion η → an injective, non-contractive map with d_H(f x, f y) ≤ η d(x, y) (Definition 1); reason: Definition 1 defines distortion for non-contractive embeddings; µ-HSTs are closed under scaling their labels, so this is equivalent to the scale-invariant reading
--   - encoding: an HST on n points; a µ-HST → `HST P` on a finite type P with n = |P|; an `HST Q` with `IsMuHST µ` (parent label ≥ µ · child label); reason: Definition 4; nodes are recorded by their sets of descendant leaves
--   - encoding: ⌈log_{µ/η} η⌉ → the integer ceiling Int.ceil of Real.logb (µ/η) η, cast to ℝ; reason: Lean notation
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 14 (PDF 18), Lemma 6

import Mathlib
import Definitions.Def_RamseyLST_Main_FiniteMetric
import Definitions.Def_RamseyLST_Main_HST

namespace RamseyLST.Main

/-- Lemma 6 (p. 14, [BLMN05, Lemma 3.15]): for `µ > η > 1` and every HST `U` on `n` points there
is a subset `S` with `|S| ≥ n^{1 − 1/⌈log_{µ/η} η⌉}` which embeds with distortion `η` into a
`µ`-HST. -/
theorem lemma_6 (mu η : ℝ) (hη : 1 < η) (hmu : η < mu) (P : Type) [Fintype P] [DecidableEq P]
    (U : HST P) :
    ∃ S : Finset P,
      (Fintype.card P : ℝ) ^ (1 - 1 / (⌈Real.logb (mu / η) η⌉ : ℝ)) ≤ (S.card : ℝ) ∧
        ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (H : HST Q) (f : S → Q),
          H.IsMuHST mu ∧ IsEmbeddingWithDistortion (fun a b : S => U.dist a b) H.dist f η := by sorry

end RamseyLST.Main
