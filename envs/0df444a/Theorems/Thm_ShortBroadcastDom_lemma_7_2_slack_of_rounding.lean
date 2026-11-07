-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_7_2_slack_of_rounding
-- name    : ShortBroadcastDom.lemma_7_2_slack_of_rounding
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:14.711186+00:00
-- url     : https://prove2.me/theorems/ba600856-2d41-4f06-adba-8a50fbcda37c
-- title:
--   Lemma 7.2 — if $|D|\le M(w+\ell)+M'P$ then $\mathcal C(x)\le(1+\delta)C^*$ forces $|D|\le C^*$
-- statement:
--   Setting (§7.1): $a\ge1$, $b=2a+1$, $t=1/(a+1)$, candidates $C$, demands $R_0\subseteq C$, costs $0<c\le b$ on $C$, and $x\in[0,1]^C$ a feasible fractional cover of $R_0$ by $C$; the sets $W,R,H,U,D,O,L$ and the numbers $w,\ell,P,\mathcal C(x)$ are those of the rounding rule.
--
--   Assume the hypotheses of Lemma 7.1 (subgraph density at most $a$, $c=b$ on $H$, $c\ge h$ on $O$), and let $C^*$ be the minimum cost of a fractional cover of $R_0$ using only candidates in $C$. Suppose that $|D|\le M(w+\ell)+M'P$ for numbers $M,M'>0$, and put
--
--   $$
--   \delta=\min\Bigl\{\frac1{(a+1)M},\frac1{M'}\Bigr\}.
--   $$
--
--   If $\mathcal C(x)\le(1+\delta)C^*$, then $|D|\le C^*$.
--
--   Differences from the source:
--   - reading: "In the setting of Lemma 7.1" → the setting of §7.1 together with the three hypotheses of Lemma 7.1; reason: the proof applies (21), which needs them
--   - encoding: C∗, the minimum cost of a fractional cover of R0 using only candidates in C → tauOn G C R₀ c (sInf over x ≥ 0 vanishing outside C); reason: R₀ ⊆ C makes the program feasible and the costs are positive, so this is the minimum
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.1, p.45 (PDF p.48), Lemma 7.2

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_RoundingData
import Definitions.Def_ShortBroadcastDom_tauOn

namespace ShortBroadcastDom

/-- **Lemma 7.2 (slack of the rounding).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §7.1, p.45 (PDF 48): "In the setting of
Lemma 7.1, let C∗ be the minimum cost of a fractional cover of R0 using only candidates in C.
Suppose that |D| ≤ M(w + ℓ) + M′P for numbers M, M′ > 0, and put δ = min{1/((a + 1)M), 1/M′}. If
C(x) ≤ (1 + δ)C∗, then |D| ≤ C∗."

**Formalization Note** "The setting of Lemma 7.1" includes its three hypotheses (subgraph density
`a`, `c = b` on `H`, `c ≥ h` on `O`); `C∗ = tauOn G C R₀ c`. The bound on `|D|` is assumed for the
given `x`. -/
theorem lemma_7_2_slack_of_rounding {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : RoundingData V) (hset : IsRoundingSetting G d) (hdens : SubgraphDensityLE d.a G)
    (hH : ∀ v ∈ d.H G, d.c v = d.b) (hO : ∀ v ∈ d.O G, (d.h G v : ℝ) ≤ d.c v)
    (M M' : ℝ) (hM : 0 < M) (hM' : 0 < M')
    (hD : ((d.D G).card : ℝ) ≤ M * ((d.wCard : ℝ) + (d.ell G : ℝ)) + M' * d.P G)
    (hC : d.cost ≤ (1 + min (1 / ((d.a + 1) * M)) (1 / M')) * tauOn G d.C d.R0 d.c) :
    ((d.D G).card : ℝ) ≤ tauOn G d.C d.R0 d.c := by sorry

end ShortBroadcastDom
