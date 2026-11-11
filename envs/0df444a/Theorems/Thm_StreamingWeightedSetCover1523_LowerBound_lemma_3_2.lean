-- Prove2me | Theorems.Thm_StreamingWeightedSetCover1523_LowerBound_lemma_3_2
-- name    : StreamingWeightedSetCover1523.LowerBound.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:11.889801+00:00
-- url     : https://prove2.me/theorems/b247e0fa-b72c-47f9-8a37-2da3c8100780
-- title:
--   Lemma 3.2 — conditioning a block biases little on average
-- statement:
--   Let $X_1,\dots,X_r$ ($r\ge1$) be independent uniform vectors in $\mathbb F_2^v$, and condition on a nonempty event $R\subseteq(\mathbb F_2^v)^r$, of probability $u=|R|/2^{rv}>0$. Let $f_i$ be the resulting density of $X_i$ relative to $U_v$,
--   $$f_i(x)=2^v\,\frac{|\{t\in R: t_i=x\}|}{|R|},$$
--   and $\bar f=r^{-1}\sum_{i=1}^r f_i$, the density of $X_I$ for an independent uniform index $I\in[r]$. Then
--   $$\mathrm{Ent}(\bar f)\le\frac{\ln(1/u)}{r}.\qquad(10)$$
--
--   $R$ is an arbitrary event of whole tuples, not a product event. The bound converts the rarity of a rectangle side into a bound on the bias of a vector at a hidden uniform position.
--
--   Differences from the source:
--   - encoding: an independent uniform index I ∈ [r]; an event of probability u > 0 → hypotheses 0 < r and R nonempty, with u = |R| / 2^{rv}; reason: nondegeneracy conditions implicit in the statement; they exclude only undefined cases
-- source:
--   Ali Vakilian, Streaming Weighted Set Cover Requires (Nearly) Linear Space, STOC 2027 submission #1523 (October 2026), Lemma 3.2, printed p. 13 (PDF p. 14), eq. (10); citation basis: submitted artifact, sha256 16f3c2dfc6183f4752aece654f17f2cb6a47fbe55659e6906ad7bd3524d6223f

import Definitions.Def_StreamingWeightedSetCover1523_LowerBound_HardInstance

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace StreamingWeightedSetCover1523.LowerBound

/-- Lemma 3.2 (PDF p. 14, eq. (10)): for `X₁, …, X_r` independent uniform on `F₂^v`, conditioned
on a nonempty event `R` of probability `u = |R| / 2^{rv}`, the average `f̄` of the conditional
marginal densities satisfies `Ent(f̄) ≤ ln(1/u) / r`. -/
theorem lemma_3_2 (v r : ℕ) (hr : 0 < r) (R : Finset (Fin r → Vec v)) (hR : R.Nonempty) :
    Ent (avgMarginal R) ≤
      Real.log (1 / ((R.card : ℝ) / (2 : ℝ) ^ (r * v))) / (r : ℝ) := by sorry

end StreamingWeightedSetCover1523.LowerBound
