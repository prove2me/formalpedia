-- Prove2me | Theorems.Thm_RobustCtxPricing_lemma_3_6
-- name    : RobustCtxPricing.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:55.615305+00:00
-- url     : https://prove2.me/theorems/c270fa9b-2a14-4206-a947-0014a91d6671
-- title:
--   Lemma 3.6 — each evidence set receives $O(d)$ insertions
-- statement:
--   There is an absolute constant $K$ with the following property. Let $d\ge1$, $T\in\mathbb N$ and $\epsilon=T^{-3}$. Let $\mathcal H=\big((u_1,p_1),\dots,(u_M,p_M)\big)$ be an evidence set built by $M\le T$ successive insertions, with every context $u_i\in\Theta$, such that each inserted context $u_i$ was **not** predicted, in the sense of (1), by the samples $(u_1,p_1),\dots,(u_{i-1},p_{i-1})$ inserted before it. Then
--   $$
--   M\le K\,d .
--   $$
--   So a single evidence set can receive only $O(d)$ pairs $(u_t,m_t)$ that it does not predict, uniformly in $T$ and in the corruption.
--
--   Differences from the source:
--   - encoding: O(d) → there is an absolute K, chosen before d and T, with M ≤ K d; reason: the meaning of O(·) here
--   - encoding: the pairs (m_t, u_t) added to 𝓗_j during the T rounds → a list of M ≤ T samples, each not predicted by the samples before it; reason: one insertion per round (the proof's "trivial bound M ≤ T", p.19); it cannot be dropped: at T = 1, d = 1 (ϵ = 1) the list 1, 1, 1, … is never predicted, since |λ| + |1 − λ| ≥ 1 > 1/8
--   - generalization: the prices m_t of the inserted pairs → arbitrary prices; reason: the prediction test (1) does not read the prices
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - encoding: the dimension d ∈ ℕ of ℝ^d → a natural number d with 1 ≤ d; reason: the context dimension of the model; d = 0 has no directions and is not an instance of it
--   - encoding: the test (1), min_λ {…} ≤ 1/(8T) → ∃ λ with ϵ‖λ‖₁ + ‖u − Σ λ_i u_i‖₂ ≤ 1/(8T); reason: for ϵ > 0 the objective is continuous and coercive, so the minimum is attained and the two tests agree
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Lemma 3.6, p.17 (proof pp.17–19)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Algorithm4

namespace RobustCtxPricing

/-- **Lemma 3.6.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §3.2.3, p.17: "Fix an evidence set index `j`. At most `O(d)` pairs
`(m_t, u_t)`, which do not satisfy Equation (1) for `u_t` and `𝓗_j`, can be added to `𝓗_j`."

There is an absolute constant `K` such that: for all `d ≥ 1` and `T`, if an evidence set
`H = [(u_1, p_1), …, (u_M, p_M)]` with contexts in `Θ` was built by insertions each of which was
not predicted (1) (with `ϵ = T⁻³`) by the samples inserted before it, and there were at most `T`
insertions (one per round), then `M ≤ K d`.

**Formalization Note.** `O(d)` is "`∃ K` absolute, quantified before `d` and `T`". The bound
`M ≤ T` is the proof's "trivial bound" (one insertion per round, p.19), stated as a hypothesis
because the lemma is about one evidence set in isolation. The test (1) reads only the stored
contexts, not the prices. -/
theorem lemma_3_6 : ∃ K : ℝ, ∀ (d T : ℕ), 1 ≤ d →
    ∀ H : List (EuclideanSpace ℝ (Fin d) × ℝ),
      (∀ s ∈ H, s.1 ∈ Theta d) →
      (∀ i : Fin H.length, ¬ Predicts (epsT T) T (H.take i) (H.get i).1) →
      H.length ≤ T →
      (H.length : ℝ) ≤ K * d := by sorry

end RobustCtxPricing
