-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_lemma_3_6
-- name    : PooledTestingAdaptivity.Gap.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:00.723339+00:00
-- url     : https://prove2.me/theorems/daf2da92-ea92-49ad-8311-99dc271064c6
-- title:
--   Lemma 3.6 — Failure invariant
-- statement:
--   Let $E$ be any finite coordinate set, let $T$ be a reduced normalized query–offer tree on $E$, and let $R\subseteq\{0,1\}^E$ be increasing in the coordinatewise order. Let $I_T$ be its stopping indicator and $F_T$ its occurrence-wise thinning failure probability. Then
--
--   $$\sum_{z\in R}F_T(z)(1+I_T(z))\le |R|.$$
--
--   The assertion covers every increasing set, including the empty set, and does not assume that $F_T$ is monotone. It includes empty coordinate sets, empty query and offer labels, and repeated offers. This invariant controls failure on all the increasing restrictions of the Boolean cube used in the paper.
--
--   Differences from the source:
--   - encoding: a finite set E and an increasing subset of its Boolean cube → an arbitrary finite type E and a Finset of functions E → Bool; reason: every finite set and every subset of its finite cube has this representation, including the empty cases
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Lemma 3.6, Eq. (7), printed p. 8, PDF p. 9; repeated proof §4.3, printed p. 15, PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_ReducedTree

namespace PooledTestingAdaptivity.Gap

/-- Lemma 3.6, printed p.8 / PDF p.9, Eq.(7), on every increasing subset. -/
theorem lemma_3_6 {E : Type} [Fintype E] [DecidableEq E]
    (T : ReducedTree E) (hT : T.Normalized) (R : Finset (E → Bool))
    (hR : Increasing R) :
    ∑ z ∈ R, T.failure z * (1 + T.stopIndicator z) ≤ (R.card : ℝ) := by sorry

end PooledTestingAdaptivity.Gap
