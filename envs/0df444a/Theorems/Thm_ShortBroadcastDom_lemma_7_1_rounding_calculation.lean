-- Prove2me | Theorems.Thm_ShortBroadcastDom_lemma_7_1_rounding_calculation
-- name    : ShortBroadcastDom.lemma_7_1_rounding_calculation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:01.380463+00:00
-- url     : https://prove2.me/theorems/51ccce71-3543-4114-b48d-f74672ba5ec9
-- title:
--   Lemma 7.1 — the rounding calculation (19)–(21)
-- statement:
--   Setting (§7.1): $a\ge1$, $b=2a+1$, $t=1/(a+1)$, candidates $C$, demands $R_0\subseteq C$, costs $0<c\le b$ on $C$, and $x\in[0,1]^C$ a feasible fractional cover of $R_0$ by $C$; the sets $W,R,H,U,D,O,L$ and the numbers $w,\ell,P,\mathcal C(x)$ are those of the rounding rule.
--
--   Suppose that every subgraph of $G$ has density at most $a$, that $c(v)=b$ for $v\in H$, and that $c(v)\ge h(v)$ for $v\in O$. Then $D$ dominates $R_0$, and
--
--   $$
--   \sum_{v\in H}\bigl(h(v)-b\bigr)+(a+1)|H\setminus R|\le a\ell,\tag{19}
--   $$
--
--   $$
--   |U|\le\sum_{v\in O}h(v)\,x_v,\tag{20}
--   $$
--
--   $$
--   \mathcal C(x)-|D|\ge\frac{w+\ell}{a+1}+P.\tag{21}
--   $$
--
--   Inequality (21) is the rounding saving, expressed through $w+\ell$ and $P$; Lemma 7.2 turns it into a slack bound.
--
--   Differences from the source:
--   - encoding: every subgraph of G has edge density at most a → SubgraphDensityLE a G (induced subgraphs); reason: an arbitrary subgraph has at most as many edges as the induced one
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.1, p.44 (PDF p.47), Lemma 7.1

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_RoundingData

namespace ShortBroadcastDom

/-- **Lemma 7.1 (the rounding calculation).** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §7.1, p.44 (PDF 47): "In the setting above,
suppose that every subgraph of G has edge density at most a, c(v) = b on H, and c(v) ≥ h(v) on O.
Then D covers R0, and ∑_{v∈H} (h(v) − b) + (a + 1)|H \ R| ≤ aℓ, (19) |U| ≤ ∑_{v∈O} h(v)xv, (20)
C(x) − |D| ≥ (w + ℓ)/(a + 1) + P. (21)"

**Formalization Note** "The setting above" is `IsRoundingSetting G d` (p.43: `a ≥ 1`, `R₀ ⊆ C`,
`0 < c ≤ b` on `C`, `x ∈ [0,1]^C` feasible for `R₀`); the sets `W, R, H, U, D, O, L` and the numbers
`w, ℓ, P, 𝒞(x)` are those of `RoundingData`. -/
theorem lemma_7_1_rounding_calculation {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : RoundingData V) (hset : IsRoundingSetting G d) (hdens : SubgraphDensityLE d.a G)
    (hH : ∀ v ∈ d.H G, d.c v = d.b) (hO : ∀ v ∈ d.O G, (d.h G v : ℝ) ≤ d.c v) :
    DominatesSet G d.R0 (d.D G) ∧
    ∑ v ∈ d.H G, ((d.h G v : ℝ) - d.b) + (d.a + 1) * ((d.H G \ d.R G).card : ℝ) ≤
      d.a * (d.ell G : ℝ) ∧
    ((d.U G).card : ℝ) ≤ ∑ v ∈ d.O G, (d.h G v : ℝ) * d.x v ∧
    ((d.wCard : ℝ) + (d.ell G : ℝ)) / (d.a + 1) + d.P G ≤ d.cost - ((d.D G).card : ℝ) := by sorry

end ShortBroadcastDom
