-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P08_remarkTwo_vanishing
-- name    : QAlgorithms.Papers.Independent.Next46.P08.remarkTwo_vanishing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:52:56.69345+00:00
-- url     : https://prove2.me/theorems/844c9285-df21-483a-bcf7-579a8a5a0edd
-- title:
--   Remark 2: the continuity expression vanishes for fixed positive t
-- statement:
--   Let $F:[0,\infty)\to\mathbb R$ satisfy the scalar majorant conditions (9)–(10): on $(0,\infty)$ it is twice differentiable, $F>0$, $F'>0$, $F''<0$, and $F(x)=o(x)$ as $x\to\infty$. Let $E\ge0$ be finite and fix $t>0$. Set $r_\varepsilon(t)=(1+t/2)/(1-\varepsilon t)$, $g(u)=(u+1)\log(u+1)-u\log u$, and $h_2(u)=-u\log u-(1-u)\log(1-u)$, with their continuous endpoint values and natural logarithms. Then $t\le 1/(2\varepsilon)$ for every sufficiently small positive $\varepsilon$, and
--
--   $$
--   \lim_{x\downarrow0}xF(E/x)=0,\qquad
--   \lim_{\varepsilon\downarrow0}\left[\varepsilon(2t+r_\varepsilon(t))F\!\left(\frac{E}{\varepsilon t}\right)+2g(\varepsilon r_\varepsilon(t))+2h_2(\varepsilon t)\right]=0.
--   $$
--
--   This is the scalar vanishing-modulus observation used in the continuity corollaries. The limit fixes $t$; it is not uniform over the whole moving admissible interval. Domination of a particular entropy envelope plays no role in this functional implication.
-- source:
--   Energy-constrained diamond norms and their use in quantum information theory, arXiv:1706.00361v2, PDF p. 11, Remark 2: vanishing optimized continuity modulus

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P08

export QAlgorithms.Papers.Independent.Claimed50.P32 (StrongChannel)

export QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble ensembleHolevo)

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Remark 2, PDF p.11 (also pp.13,18): the scaled majorant and complete
right side of (12) vanish at positive epsilon tending to zero, for each FIXED
positive t. This t is eventually admissible. No uniform limit over all
moving t, and no attained minimum, is asserted. -/
theorem remarkTwo_vanishing (F : ℝ → ℝ) (hF : MajorantRegularity F)
    (E : ℝ) (hE : 0 ≤ E) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun x : ℝ => x * F (E / x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < epsilon ∧ t ≤ 1 / (2 * epsilon)) ∧
    Tendsto (fun epsilon : ℝ => holevoBound F E epsilon t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P08

end
