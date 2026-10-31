-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_1
-- name    : PersuasionNetworks.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:41.344634+00:00
-- url     : https://prove2.me/theorems/5c9df072-33a1-4dc8-b7bc-c1f8fb4d49f0
-- title:
--   Lemma 1 — every mechanism reduces to a level mechanism with the same payoff
-- statement:
--   Let $\pi$ be a mechanism with signal $S$ on a signal space $\mathcal S$, and let $\mathcal S_k=\{s\mid\mathbb E[T\mid S=s]\in[b_k,b_{k-1})\}$. Let $S'$ be the signal on $\{1,\dots,K\}$ with $S'=k$ if $S\in\mathcal S_k$, and $S'=1$ if $S\notin\bigcup_k\mathcal S_k$. Then such a signal exists, and:
--
--   1. $\mathbb E[T\mid S'=k]\in[b_k,b_{k-1})$ for every $k$ with $\mathbb P(S'=k)>0$;
--   2. the two mechanisms yield the same expected payoff to the designer.
--
--   This reduces the designer's problem over arbitrary signal spaces to mechanisms that recommend one level of the step function.
--
--   **Formalization Note** The mechanism $\pi'$ is the push-forward of the kernel along the map $f$ with $S'=f(S)$. The statement covers every measurable $f$ with these two properties; they determine $f$ because the sets $\mathcal S_k$ are disjoint.
--
--   Differences from the source:
--   - generalization: π′ is given → existence of a measurable f with (a), (b) is also claimed; reason: the page assumes π′; dropping the clause gives the printed claim
--   - encoding: the signal S′ of π′ → the kernel κ.map f for measurable f; signal space ℕ with all mass on {1, …, K}; reason: S′ = f(S) by (a), (b); ℕ is only a carrier
--   - encoding: clause 1 → IsLevelMechanism (κ.map f); reason: the definition is clause 1 plus the signal set of (a), (b)
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Lemma 1, p.16

import Mathlib
import Definitions.Def_PersuasionNetworks_Mechanism

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Lemma 1**, Candogan, SSRN 3346144 (preprint), p.16. Let `κ` be a mechanism with signal space `S` and let
`S_k = {s | E[T | S = s] ∈ [b_k, b_{k-1})}`. Let `S' = f(S)`, where `f` sends `S_k` to `k` and sends
every `s ∉ ⋃_k S_k` to `1`. Such an `f` exists and is measurable; and for it, (1) the mechanism `S'`
is a level mechanism, and (2) it yields the same expected payoff as `κ`.

**Formalization Note.** The page's `π'` is the mechanism `κ.map f`, the signal `S'` being the
function `f` of `S`. A level mechanism carries clause 1 of the page (`IsLevelMechanism`). The
existence clause is added: the `S_k` are disjoint and the page takes `π'` as given. -/
theorem lemma_1 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    {S : Type*} [MeasurableSpace S] (κ : Kernel ℝ S) [IsMarkovKernel κ] :
    (∃ f : S → ℕ, Measurable f ∧
      (∀ k ∈ Finset.Icc 1 K, ∀ s, InBand b k (posteriorMean μ κ s) → f s = k) ∧
      (∀ s, (∀ k ∈ Finset.Icc 1 K, ¬ InBand b k (posteriorMean μ κ s)) → f s = 1)) ∧
    ∀ f : S → ℕ, Measurable f →
      (∀ k ∈ Finset.Icc 1 K, ∀ s, InBand b k (posteriorMean μ κ s) → f s = k) →
      (∀ s, (∀ k ∈ Finset.Icc 1 K, ¬ InBand b k (posteriorMean μ κ s)) → f s = 1) →
      IsLevelMechanism μ K b (κ.map f) ∧
        designerPayoff μ (nu K b r) (κ.map f) = designerPayoff μ (nu K b r) κ := by sorry

end PersuasionNetworks
