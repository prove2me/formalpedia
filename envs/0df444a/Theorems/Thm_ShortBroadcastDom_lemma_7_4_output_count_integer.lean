-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_7_4_output_count_integer
-- name    : ShortBroadcastDom.lemma_7_4_output_count_integer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:44.729005+00:00
-- url     : https://prove2.me/theorems/13648959-f2ad-4949-a125-ea75fdf42d79
-- title:
--   Lemma 7.4 — output count in the integer case: $|D|\le b^2(w+\ell)+db^2P$
-- statement:
--   Let $d=2a$ be an integer with $a\ge1$, $b=d+1$, and $G\in\mathcal C_a$. Take the first selection $F$, demands $R_0$ and costs $c$ of §7.2, and apply the rounding rule of §7.1 in $G$ with candidate set $C=V(G)\setminus F$. Then for every vector $x\in[0,1]^{V(G)\setminus F}$ that is a feasible fractional cover of $R_0$ (i.e. $\sum_{v\in N_G[r]\setminus F}x_v\ge1$ for $r\in R_0$),
--
--   $$
--   |D|\le b^2(w+\ell)+d\,b^2P.
--   $$
--
--   With Lemma 7.2 ($M=b^2$, $M'=db^2$) this gives the slack $\delta=1/(2a(2a+1)^2)$ of the integer case; the minor-density bound is used here and only here.
--
--   Differences from the source:
--   - encoding: d = 2a an integer, a ≥ 1, G ∈ C_a → d : ℕ with 2 ≤ d and InClassC (d/2) G; reason: the same parameters
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.2, p.46 (PDF p.49), Lemma 7.4

import Mathlib
import Definitions.Def_ShortBroadcastDom_InClassC
import Definitions.Def_ShortBroadcastDom_firstSel

namespace ShortBroadcastDom

/-- **Lemma 7.4 (output count, integer case).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §7.2, p.46 (PDF 49): "For every feasible
vector x on V(G) \ F, |D| ≤ b²(w + ℓ) + db²P."

Setting (pp.45–46): `d = 2a` an integer with `a ≥ 1`, `b = d + 1`, `G ∈ C_a` (the minor-density
bound is used here), the first selection `F`, demands `R₀`, costs `c` of §7.2, and the rounding rule
of §7.1 applied in `G` with `C = V(G) \ F`.

**Formalization Note** "Feasible on `V(G) \ F`" is `IsFeasibleOn G (V \ F) R₀ x`:
`x ∈ [0,1]^(V \ F)` and `∑_{v ∈ N_G[r] \ F} x_v ≥ 1` for `r ∈ R₀`. The sets and numbers are
those of `selRounding G d x`. -/
theorem lemma_7_4_output_count_integer {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 2 ≤ d) (hG : InClassC ((d : ℝ) / 2) G) (x : V → ℝ)
    (hx : IsFeasibleOn G (Finset.univ \ firstSel G d) (remDemands G d) x) :
    (((selRounding G d x).D G).card : ℝ) ≤
      ((d : ℝ) + 1) ^ 2 * (((selRounding G d x).wCard : ℝ) + ((selRounding G d x).ell G : ℝ)) +
        (d : ℝ) * ((d : ℝ) + 1) ^ 2 * (selRounding G d x).P G := by sorry

end ShortBroadcastDom
