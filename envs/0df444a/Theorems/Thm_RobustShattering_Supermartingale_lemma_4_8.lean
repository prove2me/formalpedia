-- Prove2me | Theorems.Thm_RobustShattering_Supermartingale_lemma_4_8
-- name    : RobustShattering.Supermartingale.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:43:41.300283+00:00
-- url     : https://prove2.me/theorems/9db7c048-0758-47ec-aa15-a572b51880b8
-- title:
--   Lemma 4.8 — one step of the product of cost functions over a 2c-independent set is a supermartingale step
-- statement:
--   Let $X\in\mathbb R_{\ge0}$, $Y\in\mathbb R_{>0}$, $c\in\mathbb N$, and consider a $(c,X,Y)$-shatterable $T$-step process on a finite graph $G$ (Definition 4.7) with cost functions $\gamma_{v,i}$. Let $S\subseteq V$ be $2c$-independent (pairwise distance greater than $2c$ in $G$) and $i\in\{0,\dots,T-1\}$. Then for every fixed $R_{\le i}$,
--   $$\mathop{\mathbb E}_{R_{i+1}(B^c(S))}\Big[\prod_{v\in S}\gamma_{v,i+1}(R_{\le i},R_{i+1}(B^c(v)))\Big]\le\prod_{v\in S}\gamma_{v,i}(R_{\le i-1},R_i(B^c(v))).$$
--
--   The lemma says that the product of the cost functions over a $2c$-independent set inherits the local supermartingale property of the single costs: the $c$-balls around the nodes of $S$ are disjoint, so the factors depend on disjoint blocks of the fresh randomness. It is the step from which Lemma 4.9 follows by induction.
--
--   **Formalization Note.** The history is a full point $\omega$ of the randomness; the expectation is the lower Lebesgue integral over $\eta\sim\prod_{u\in V}\mu_{u,i}$ (Lean step $i$ = the paper's step $i+1$) of the product of the $\mathbb R_{\ge0}$-valued costs coerced to $[0,\infty]$, evaluated at $\omega$ with its step-$(i+1)$ coordinates replaced by $\eta$.
--
--   Differences from the source:
--   - encoding: expectation over $R_{i+1}(B^c(S))$ for fixed $R_{\le i}$ → lower Lebesgue integral over the step-$(i+1)$ randomness of all nodes, every other coordinate of $\omega$ kept fixed; reason: the integrand depends on the step-$(i+1)$ randomness only through $R_{i+1}(B^c(S))$, and the remaining coordinates integrate out against probability measures, so the value is the same
--   - encoding: steps $1,\dots,T$ → `Fin T` with Lean step $k$ = the paper's step $k+1$; costs indexed by $\mathbb N$ with only $i\le T$ constrained; reason: index shift only
--   - encoding: expectations of $\mathbb R_{\ge0}$-valued costs → `lintegral` of the $[0,\infty]$-valued coercion, the costs being measurable (part of Definition 4.7's encoding); reason: the paper's expectations presuppose measurability, and `lintegral` has no junk zero
-- source:
--   Davies-Peck, Ghaffari, Halldórsson, Maus, Nolin, Robust Shattering Arguments, arXiv:2606.27847 (held manuscript, sha256 21726e7f…8128), p. 15, Lemma 4.8

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_RobustShattering_Supermartingale_Shatterable

open MeasureTheory
open scoped ENNReal NNReal

namespace RobustShattering.Supermartingale

/-- Lemma 4.8 (p. 15): for a `(c, X, Y)`-shatterable `T`-step process with cost functions `γ`,
a `2c`-independent set `S` and `i ∈ {0, …, T - 1}`, for every fixed history `ω`, the integral over
the fresh randomness `η` of all nodes in the paper's step `i + 1` (Lean step `i`) of
`∏_{v ∈ S} γ_{v,i+1}` is at most `∏_{v ∈ S} γ_{v,i}(ω)`. -/
theorem lemma_4_8 {V : Type} [Fintype V] (G : SimpleGraph V) {T : ℕ}
    {Ω : V → Fin T → Type} [∀ u k, MeasurableSpace (Ω u k)]
    (μ : ∀ u k, Measure (Ω u k)) [∀ u k, IsProbabilityMeasure (μ u k)]
    (c : ℕ) (X Y : ℝ≥0) (hY : 0 < Y) (B : Randomness Ω → Set V)
    (γ : V → ℕ → Randomness Ω → ℝ≥0) (hγ : IsShatteringCost G c X Y μ B γ)
    (S : Finset V) (hS : LocalLLL.Main.separated G (2 * c) (S : Set V))
    (i : ℕ) (hi : i < T) (ω : Randomness Ω) :
    ∫⁻ η, ∏ v ∈ S, (γ v (i + 1) (Function.update ω ⟨i, hi⟩ η) : ℝ≥0∞)
        ∂(Measure.pi (fun u : V => μ u ⟨i, hi⟩)) ≤ ∏ v ∈ S, (γ v i ω : ℝ≥0∞) := by sorry

end RobustShattering.Supermartingale
