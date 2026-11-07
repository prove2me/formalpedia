-- Prove2me | Theorems.Thm_ShortBroadcastDom_sec_7_3_output_count_noninteger
-- name    : ShortBroadcastDom.sec_7_3_output_count_noninteger
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:54.665202+00:00
-- url     : https://prove2.me/theorems/68f6f7de-6963-4f81-9f34-e8b843470acd
-- title:
--   §7.3 — output count in the non-integer case: $|D|\le\frac{a}{1-\theta}(w+\ell)+\frac{k+1}{\theta}P$
-- statement:
--   Let $a\ge1$ be rational with $2a\notin\mathbb Z$, put $k=\lfloor2a\rfloor$ and $\theta=2a-k\in(0,1)$, and let $G$ be a finite graph all of whose subgraphs have density at most $a$. Apply the rounding rule of §7.1 with $C=R_0=V(G)$ and constant costs $c\equiv b=2a+1$ to a feasible fractional dominating vector $x\in[0,1]^{V(G)}$. Then
--
--   $$
--   |D|\le M(w+\ell)+M'P,\qquad M=\frac{a}{1-\theta},\quad M'=\frac{k+1}{\theta}.
--   $$
--
--   With Lemma 7.2 this gives the slack $\delta=\min\{(1-\theta)/(a(a+1)),\ \theta/(k+1)\}$ of the non-integer case.
--
--   Differences from the source:
--   - generalization: G ∈ C_ρ for a fixed rational ρ ≥ a, and every subgraph of G has density at most a → only: every subgraph of G has density at most a; reason: the computation uses only the subgraph-density bound (via (19) and (20)); adding G ∈ C_ρ gives the paper's setting
-- source:
--   Amiri, Siebertz, Wawrzyniak, Paying for Fractional Error: Tight Constant-Round Approximation of Covering Problems with Short Broadcasts (arXiv:2611.02057, sha256 f4dc98d2cf73d74a105e5b0e61c4b72d15ae82b3f202490e2e4ecf864b40646a), §7.3, p.47 (PDF p.50), display "Hence |D| = w + |H| + |U| ≤ M(w + ℓ) + M′P"

import Mathlib
import Definitions.Def_ShortBroadcastDom_SubgraphDensityLE
import Definitions.Def_ShortBroadcastDom_RoundingData

namespace ShortBroadcastDom

/-- **§7.3, output count in the non-integer case.** Amiri, Siebertz, Wawrzyniak, *Paying for Fractional Error* (arXiv:2611.02057, sha256 prefix
f4dc98d2), §7.3, p.47 (PDF 50), display "Hence
|D| = w + |H| + |U| ≤ M(w + ℓ) + M′P": "Each h(v) is an integer. On H, h(v) ≥ b = k + 1 + θ, so
h(v) − b ≥ 1 − θ, and (19) gives (1 − θ)|H| ≤ aℓ. On O, h(v) ≤ k + 1 and c(v) − h(v) ≥ θ, so (20)
gives |U| ≤ (k + 1)P/θ. Hence |D| = w + |H| + |U| ≤ M(w + ℓ) + M′P, M = a/(1 − θ),
M′ = (k + 1)/θ, using M ≥ 1."

Setting (p.47): `2a` is not an integer, every subgraph of `G` has density at most `a`,
`k = ⌊2a⌋`, `θ = 2a − k ∈ (0, 1)`, and the rounding rule of Lemma 7.1 with `C = R₀ = V(G)` and
constant costs `c ≡ b = 2a + 1`, applied to a feasible `x ∈ [0, 1]^V(G)`.

**Formalization Note** The sets and numbers are those of `uniformRounding a x`. The hypothesis
`G ∈ C_ρ` of the section is not assumed; the bound uses only the subgraph density. -/
theorem sec_7_3_output_count_noninteger {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : ℚ) (ha : 1 ≤ a) (hna : ∀ m : ℤ, 2 * a ≠ m) (hG : SubgraphDensityLE (a : ℝ) G)
    (x : V → ℝ) (hx : IsFeasibleOn G Finset.univ Finset.univ x) :
    (((uniformRounding (a : ℝ) x).D G).card : ℝ) ≤
      (a : ℝ) / (1 - ((2 * a : ℚ) - ⌊2 * a⌋ : ℝ)) *
          (((uniformRounding (a : ℝ) x).wCard : ℝ) + ((uniformRounding (a : ℝ) x).ell G : ℝ)) +
        ((⌊2 * a⌋ : ℝ) + 1) / ((2 * a : ℚ) - ⌊2 * a⌋ : ℝ) * (uniformRounding (a : ℝ) x).P G := by sorry

end ShortBroadcastDom
