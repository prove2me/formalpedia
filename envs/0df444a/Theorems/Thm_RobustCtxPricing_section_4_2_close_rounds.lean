-- Prove2me | Theorems.Thm_RobustCtxPricing_section_4_2_close_rounds
-- name    : RobustCtxPricing.section_4_2_close_rounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:00:04.370744+00:00
-- url     : https://prove2.me/theorems/850e81d9-12a6-4f4e-b8f4-dba29360d2c5
-- title:
--   §4.2 (third bullet) — $O((\bar C+1)d)$ exploration rounds with $x_t=1$ in Algorithm 4
-- statement:
--   There is an absolute constant $K$ with the following property. Let $d\ge1$, $T,C\in\mathbb N$, $\theta^\star\in\Theta$, contexts $u_1,\dots,u_T\in\Theta$ with $\langle\theta^\star,u_t\rangle\ge0$, and consider any run of Algorithm 4 (with $\bar C=\lceil5C+20d\log T\rceil$, $\epsilon=T^{-3}$) whose observed feedback differs from the true sale bit in at most $C$ rounds. Then the number of exploration rounds (rounds in which some evidence set does not predict $u_t$) with $x_t=1$, i.e. $|p_t-\langle\theta^\star,u_t\rangle|\le\epsilon$, is at most
--   $$
--   K\,(\bar C+1)\,d .
--   $$
--   Together with Lemma 3.5 this bounds the number of exploration rounds of Algorithm 4.
--
--   Differences from the source:
--   - encoding: O((C̄ + 1)d) → there is an absolute K, chosen before every other variable, with count ≤ K(C̄+1)d; reason: the meaning of O(·) here
--   - generalization: Algorithm 4 (no tie-breaking fixed) → every run under every tie-break; reason: specializes to any fixed rule
--   - encoding: the adaptive adversary of §2.2 → all context and feedback sequences, with the corruption constraint evaluated on the run's own prices; reason: the run is determined by the contexts, the feedback and the tie-breaking choices
--   - reading: "the number of rounds in which the (not observed) x_t = 1" → the number of exploration rounds with |p_t − ⟨θ⋆, u_t⟩| ≤ ϵ; reason: Lemma 3.7 (p.19) and the proof of Theorem 4.2 (p.21) count exploration rounds; a commit round may also have x_t = 1, and the bound is not about those
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - encoding: the dimension d ∈ ℕ of ℝ^d → a natural number d with 1 ≤ d; reason: the context dimension of the model; d = 0 has no directions and is not an instance of it
--   - reading: the budget C, an upper bound on the number of corrupted rounds (its type is not stated) → C ∈ ℕ; reason: it bounds the count |S|
--   - reading: log → the natural logarithm Real.log; reason: the base is not stated; natural log is the standard meaning, and the constants of p.17 hold with it
--   - encoding: rounds t = 1, …, T and bits in {0, 1} → rounds 0, …, T − 1 of ℕ-indexed sequences and Bool bits; reason: Lean convention; same instances
--   - encoding: the test (1), min_λ {…} ≤ 1/(8T) → ∃ λ with ϵ‖λ‖₁ + ‖u − Σ λ_i u_i‖₂ ≤ 1/(8T); reason: for ϵ > 0 the objective is continuous and coercive, so the minimum is attained and the two tests agree
--   - encoding: evidence sets 𝓗_1, …, 𝓗_{2C̄+1} → lists of samples in insertion order, indexed by Fin (2C̄+1); reason: Lean convention; a repeated sample changes neither the test (1) nor the estimate
--   - encoding: "(C̄ + 1)-st largest lower endpoint" → the entry with index C̄ of the lower endpoints sorted non-increasingly; reason: Lean convention; same instances
--   - encoding: the cases of Update-Density overlap on the hyperplanes ⟨u_t, θ⟩ = m_t ± ϵ/2 → the window case takes priority there; reason: the page leaves the overlap open; for u_t ≠ 0 the hyperplanes are null, and for u_t = 0 a window median of a positive mass has |m_t| < ϵ/2, so they do not meet the update
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §4.2, third bullet, p.21

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Algorithm4

namespace RobustCtxPricing

/-- **§4.2, third bullet.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust
Contextual Pricing*, arXiv:2607.11210, §4.2, p.21: "Thanks to Lemma 3.6, an argument similar to
Lemma 3.7 shows that the number of rounds in which the (not observed) `x_t = 1` is `O((C̄ + 1)d)`".

There is an absolute constant `K` such that for every `d ≥ 1`, horizon `T`, budget `C`, parameter
`θ⋆ ∈ Θ`, contexts `u_t ∈ Θ` with `⟨θ⋆, u_t⟩ ≥ 0`, observed feedback `Y` and run of Algorithm 4
whose feedback is corrupted in at most `C` rounds, the number of exploration rounds (some `𝓗_j`
does not predict `u_t`) in which `x_t = 1`, i.e. `|p_t − ⟨θ⋆, u_t⟩| ≤ ϵ` with `ϵ = T⁻³`, is at most
`K (C̄ + 1) d`, where `C̄ = ⌈5C + 20d log T⌉`.

**Formalization Note.** `O(·)` is "`∃ K` absolute, quantified before every other variable". The
exploration rounds of the bullet are the rounds not resolved by Commit (Algorithm 4, Line 6). -/
theorem section_4_2_close_rounds : ∃ K : ℝ, ∀ (d T C : ℕ), 1 ≤ d →
    ∀ θ : EuclideanSpace ℝ (Fin d), θ ∈ Theta d →
    ∀ u : ℕ → EuclideanSpace ℝ (Fin d), (∀ t < T, u t ∈ Theta d) →
      (∀ t < T, 0 ≤ inner ℝ θ (u t)) →
    ∀ (Y : ℕ → Bool) (r : Run d (2 * cbar d T C + 1)),
      IsAlg4Run T C u Y r → IsCorrupted T C θ u r.p Y →
      (({t | t < T ∧ (¬ ∀ j, Predicts (epsT T) T (r.H t j) (u t)) ∧
          |r.p t - inner ℝ θ (u t)| ≤ epsT T}.ncard : ℕ) : ℝ) ≤
        K * ((cbar d T C : ℝ) + 1) * d := by sorry

end RobustCtxPricing
