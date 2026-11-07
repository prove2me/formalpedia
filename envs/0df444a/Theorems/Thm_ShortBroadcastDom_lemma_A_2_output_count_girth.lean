-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_A_2_output_count_girth
-- name    : ShortBroadcastDom.lemma_A_2_output_count_girth
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:45.695108+00:00
-- url     : https://prove2.me/theorems/e697b8f2-de7d-48d9-8a1b-0f8caff9ae64
-- title:
--   Lemma A.2 — output count at girth four and six: $|D|\le b^2(w+\ell)+db^2P$, resp. $|D|\le41(w+\ell)+63P$
-- statement:
--   Let $g\in\{4,6\}$, $a=g/(g-2)$, $d=2a$ and $b=d+1$ (so $d=4$, $b=5$ for $g=4$ and $d=3$, $b=4$ for $g=6$). Let $G$ be a finite planar graph of girth at least $g$, take the first selection $F$, demands $R_0$ and costs $c$ of §7.2 for this $d$, and apply the rounding rule of §7.1 in $G$ with $C=V(G)\setminus F$. For every feasible fractional cover $x\in[0,1]^{V(G)\setminus F}$ of $R_0$,
--
--   $$
--   |D|\le b^2(w+\ell)+d\,b^2P=25(w+\ell)+100P\quad(g=4),\qquad |D|\le 41(w+\ell)+63P\quad(g=6).
--   $$
--
--   This replaces Lemma 7.4 at the two girths where $2a$ is an integer but contractions destroy the girth bound.
--
--   Differences from the source:
--   - encoding: b²(w + ℓ) + db²P for g = 4 → 5²(w + ℓ) + 4·5²P with the rounding data of d = 4; reason: b = 5 and d = 4 at g = 4
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), App. A.2, p.62 (PDF p.65), Lemma A.2

import Mathlib
import Definitions.Def_ShortBroadcastDom_firstSel
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar

namespace ShortBroadcastDom

/-- **Lemma A.2 (output count at girths four and six).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), App. A.2, p.62 (PDF 65): "For every
feasible vector x on V(G) \ F, |D| ≤ b²(w + ℓ) + db²P for g = 4, and |D| ≤ 41(w + ℓ) + 63P for
g = 6."

Setting (p.62): `g ∈ {4, 6}`, `a = g/(g − 2)` (so `d = 2a = 4`, `b = 5` at `g = 4` and `d = 3`,
`b = 4` at `g = 6`), `G` planar of girth at least `g`, the construction of §7.2 (`F`, `R₀`, `c`) and
the rounding rule of §7.1 with `C = V(G) \ F`.

**Formalization Note** The sets and numbers are those of `selRounding G d x` with `d = 4`, resp.
`d = 3`; at `g = 4` the bound `b²(w+ℓ) + db²P` is written with `b = 5`, `d = 4`. -/
theorem lemma_A_2_output_count_girth {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hP : RobertsonSeymour1986.GM5.IsPlanar G) (x : V → ℝ) :
    ((4 : ℕ∞) ≤ G.egirth →
      IsFeasibleOn G (Finset.univ \ firstSel G 4) (remDemands G 4) x →
        (((selRounding G 4 x).D G).card : ℝ) ≤
          (5 : ℝ) ^ 2 * (((selRounding G 4 x).wCard : ℝ) + ((selRounding G 4 x).ell G : ℝ)) +
            4 * (5 : ℝ) ^ 2 * (selRounding G 4 x).P G) ∧
    ((6 : ℕ∞) ≤ G.egirth →
      IsFeasibleOn G (Finset.univ \ firstSel G 3) (remDemands G 3) x →
        (((selRounding G 3 x).D G).card : ℝ) ≤
          41 * (((selRounding G 3 x).wCard : ℝ) + ((selRounding G 3 x).ell G : ℝ)) +
            63 * (selRounding G 3 x).P G) := by sorry

end ShortBroadcastDom
