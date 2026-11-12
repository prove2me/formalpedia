-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_lemma_4_9
-- name    : RobustShattering.Supermartingale.lemma_4_9
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T20:43:44.136373+00:00
-- url     : https://prove2.me/theorems/72df63f2-3b92-4e5f-8d54-f99843513317
-- title:
--   Lemma 4.9 — the expected product of cost functions over a 2c-independent set never exceeds X^|S|
-- statement:
--   Let $X\in\mathbb R_{\ge0}$, $Y\in\mathbb R_{>0}$, $c\in\mathbb N$, and consider a $(c,X,Y)$-shatterable $T$-step process on a finite graph $G$ (Definition 4.7) with cost functions $\gamma_{v,i}$. For every $2c$-independent set $S\subseteq V$ and every $i\in\{0,\dots,T\}$,
--   $$\mathop{\mathbb E}_{R_{\le i}}\Big[\prod_{v\in S}\gamma_{v,i}(R_{\le i-1},R_i(B^c(v)))\Big]\le X^{|S|}.$$
--
--   The product of the costs over $S$ is a supermartingale in the step index (Lemma 4.8) that starts at most at $X^{|S|}$ (low initial cost); this lemma bounds its expectation at every step, and at $i=T$ it feeds Markov's inequality in Lemma 4.10.
--
--   **Formalization Note.** The expectation is the lower Lebesgue integral against the joint law `processMeasure μ` of all the randomness, of the product of the $\mathbb R_{\ge0}$-valued costs coerced to $[0,\infty]$; $X^{|S|}$ is computed in $[0,\infty]$ (with $X^0=1$).
--
--   Differences from the source:
--   - encoding: expectation over $R_{\le i}$ → lower Lebesgue integral against the product law of all the randomness (steps $1,\dots,T$); reason: by locality the integrand depends only on $R_{\le i}$, and the later coordinates integrate out against probability measures, so the value is the same
--   - encoding: steps $1,\dots,T$ → `Fin T` with Lean step $k$ = the paper's step $k+1$; costs indexed by $\mathbb N$ with only $i\le T$ constrained; reason: index shift only
--   - encoding: expectations of $\mathbb R_{\ge0}$-valued costs → `lintegral` of the $[0,\infty]$-valued coercion, the costs being measurable (part of Definition 4.7's encoding); reason: the paper's expectations presuppose measurability, and `lintegral` has no junk zero
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 15, Lemma 4.9

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_Shatterable

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Supermartingale

/-- Lemma 4.9 (p. 15): for a `(c, X, Y)`-shatterable `T`-step process with cost functions `γ`,
a `2c`-independent set `S` and `i ∈ {0, …, T}`, the expectation of `∏_{v ∈ S} γ_{v,i}` under the
joint law of all the randomness is at most `X^{|S|}`. -/
theorem lemma_4_9 {V : Type} [Fintype V] (G : SimpleGraph V) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (c : ℕ) (X Y : ℝ≥0) (hY : 0 < Y) (B : Randomness Ω → Set V)
    (γ : V → ℕ → Randomness Ω → ℝ≥0) (hγ : IsShatteringCost G c X Y μ B γ)
    (S : Finset V) (hS : LocalLLL.Main.separated G (2 * c) (S : Set V))
    (i : ℕ) (hi : i ≤ T) :
    ∫⁻ ω, ∏ v ∈ S, (γ v i ω : ℝ≥0∞) ∂(processMeasure μ) ≤ (X : ℝ≥0∞) ^ S.card := by sorry

end RobustShattering.Supermartingale
