-- Prove2me | Theorems.Thm_PersuasionNetworks_lemma_2
-- name    : PersuasionNetworks.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:46.79998+00:00
-- url     : https://prove2.me/theorems/6c8adcc9-2a93-4aad-b866-98a71524b047
-- title:
--   Lemma 2 — the tuple of a level mechanism satisfies (7), (8) and pays $\sum_k p_kr_k$
-- statement:
--   Let $\pi$ be a level mechanism with signal $S$ on $\mathcal S=\{1,\dots,K\}$, and let $p_k=\mathbb P(S=k)$, $z_k=\mathbb E[T\cdot\mathbf 1\{S=k\}]$. Then:
--
--   1. $b_kp_k\le z_k$ for $k\in\mathcal S$;
--   2. for every $L\subset\mathcal S$,
--   $$
--   \sum_{k\in L}z_k\le\int_{1-\sum_{k\in L}p_k}^{1}F^{-1}(x)\,dx;
--   $$
--   3. the designer's expected payoff is $\sum_{k\in\mathcal S}p_kr_k$.
--
--   These are the properties that motivate the constraints and the objective of (OPT). Inequality (8) holds for every subset $L$, though (OPT) imposes it only on initial segments.
--
--   Differences from the source:
--   - encoding: b_k p_k ≤ z_k for k ∈ 𝒮 → guard b_k ≠ −∞ on the real product; reason: footnote 17 omits the constraint when b_K = −∞; the product is otherwise undefined
--   - encoding: signal set 𝒮 = {1, …, K} → kernel into ℕ with all mass on {1, …, K}; reason: ℕ is only a carrier
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Lemma 2, (7), (8), p.16

import Mathlib
import Definitions.Def_PersuasionNetworks_Quantile
import Definitions.Def_PersuasionNetworks_Mechanism
import Definitions.Def_PersuasionNetworks_OPT

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **Lemma 2**, Candogan, SSRN 3346144 (preprint), p.16, (7), (8). For a level mechanism with its tuple `p_k = P(S = k)`,
`z_k = E[T · 1{S = k}]`:

1. `b_k p_k ≤ z_k` (7), for `k ∈ 𝒮`;
2. `∑_{k ∈ L} z_k ≤ ∫_{1 - ∑_{k ∈ L} p_k}^{1} F⁻¹(x) dx` (8), for every `L ⊂ 𝒮`;
3. the designer's expected payoff is `∑_{k ∈ 𝒮} p_k r_k`.

**Formalization Note.** Clause 1 at `k = K` with `b_K = -∞` is vacuous (footnote 17). Clause 2 holds
for every subset, not only initial segments. -/
theorem lemma_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    (κ : Kernel ℝ ℕ) [IsMarkovKernel κ] (hκ : IsLevelMechanism μ K b κ) :
    (∀ k ∈ Finset.Icc 1 K, b k ≠ ⊥ → (b k).toReal * signalProb μ κ k ≤ signalMoment μ κ k) ∧
    (∀ L ⊆ Finset.Icc 1 K,
      ∑ k ∈ L, signalMoment μ κ k ≤ g μ 𝒯 (∑ k ∈ L, signalProb μ κ k)) ∧
    designerPayoff μ (nu K b r) κ = objective K r (signalProb μ κ) := by sorry

end PersuasionNetworks
