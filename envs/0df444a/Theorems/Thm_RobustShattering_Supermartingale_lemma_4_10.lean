-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_lemma_4_10
-- name    : RobustShattering.Supermartingale.lemma_4_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T20:43:41.833539+00:00
-- url     : https://prove2.me/theorems/8173a8cf-aa85-40b0-aafb-19c5aeb6c4d4
-- title:
--   Lemma 4.10 — a 2c-independent set joins post-shattering with probability at most (X/Y)^|S|
-- statement:
--   Let $X\in\mathbb R_{\ge0}$, $Y\in\mathbb R_{>0}$, $c\in\mathbb N$, and consider a $(c,X,Y)$-shatterable $T$-step process on a finite graph $G$ (Definition 4.7) with post-shattering set $B$. For every $2c$-independent set $S\subseteq V$,
--   $$\Pr[S\subseteq B]\le\Big(\frac XY\Big)^{|S|}.$$
--
--   This is the **separated-set bound**: although the events $[v\in B]$ need not be independent, nor determined by bounded-radius randomness, nodes that are pairwise far apart join the post-shattering set jointly with probability that decays geometrically in their number. It is Part 1 of Theorem 4.11 and the hypothesis that Lemma 4.3 and Corollary 4.4 turn into small components.
--
--   **Formalization Note.** The probability is the measure under the joint law `processMeasure μ` of $\{\omega : S\subseteq B(\omega)\}$. Since $B$ is an arbitrary function of the randomness, this set need not be measurable; the bound is then a bound on its outer measure, which is at least as strong. $(X/Y)^{|S|}$ is computed in $\mathbb R_{\ge0}$ and coerced, with $0^0=1$.
--
--   Differences from the source:
--   - encoding: $\Pr[S\subseteq B]$ → the (outer) measure of $\{\omega : S\subseteq B(\omega)\}$ under the product law, with no measurability of $B$; reason: equal to the probability when the event is measurable, and the outer-measure bound is at least as strong
--   - encoding: steps $1,\dots,T$ → `Fin T` with Lean step $k$ = the paper's step $k+1$, costs measurable and integrated with `lintegral` (Definition 4.7's encoding); reason: index shift and the standing measurability of the paper's expectations
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 16, Lemma 4.10

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_Shatterable

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Supermartingale

/-- Lemma 4.10 (p. 16): for a `(c, X, Y)`-shatterable `T`-step process with post-shattering set
`B` and any `2c`-independent set `S`, the probability that `S ⊆ B` is at most `(X / Y)^{|S|}`
(an upper bound on the outer measure; no measurability of `B` is assumed). -/
theorem lemma_4_10 {V : Type} [Fintype V] (G : SimpleGraph V) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (c : ℕ) (X Y : ℝ≥0) (hY : 0 < Y) (B : Randomness Ω → Set V)
    (hP : Shatterable G c X Y μ B)
    (S : Finset V) (hS : LocalLLL.Main.separated G (2 * c) (S : Set V)) :
    processMeasure μ {ω | (S : Set V) ⊆ B ω} ≤ (((X / Y) ^ S.card : ℝ≥0) : ℝ≥0∞) := by sorry

end RobustShattering.Supermartingale
