-- Prove2me | Theorems.Thm_RobustCtxPricing_lemma_4_1
-- name    : RobustCtxPricing.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:56.662343+00:00
-- url     : https://prove2.me/theorems/789d3072-dffb-40c6-92c5-3de6659884ad
-- title:
--   Lemma 4.1 — in Algorithm 4 at most $\bar C$ evidence sets are not correct
-- statement:
--   Let $d\ge1$, $T,C\in\mathbb N$, $\theta^\star\in\Theta$, and contexts $u_1,\dots,u_T\in\Theta$ with $\langle\theta^\star,u_t\rangle\ge0$. Consider any run of Algorithm 4 (with $\bar C=\lceil5C+20d\log T\rceil$ and $\epsilon=T^{-3}$) on these contexts whose observed feedback differs from the true sale bit $\mathbb I\{p_t\le\langle\theta^\star,u_t\rangle\}$ in at most $C$ rounds. Then at the start of every round, and after the last one,
--   $$
--   \#\{j\le 2\bar C+1:\ \mathcal H_j\text{ is not correct}\}\le\bar C ,
--   $$
--   where correctness is Definition 3.1 with $\epsilon=T^{-3}$. This is what lets Lemma 3.4 apply to every commit round of Algorithm 4.
--
--   Differences from the source:
--   - generalization: Algorithm 4 (the paper fixes no tie-breaking) → every run of Algorithm 4 under every tie-break (median, receiving set, coefficients of the commit); reason: specializes to any fixed rule
--   - encoding: the adaptive adversary of §2.2 → all context and feedback sequences, with the corruption constraint evaluated on the run's own prices; reason: the run is determined by the contexts, the feedback and the tie-breaking choices
--   - encoding: "the number of non-correct evidence sets" → the count at the start of every round t ≤ T, the state after the last round included; reason: the page's claim holds at every time of the run
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
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Lemma 4.1, p.20 (Algorithm 4, p.21)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Algorithm4

namespace RobustCtxPricing

/-- **Lemma 4.1.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §4.2, p.20: "In Algorithm 4, the number of non-correct evidence sets is
upper bounded by `C̄`."

For every `d ≥ 1`, horizon `T`, budget `C`, parameter `θ⋆ ∈ Θ`, contexts `u_t ∈ Θ` with
`⟨θ⋆, u_t⟩ ≥ 0`, observed feedback `Y` and run of Algorithm 4 (with `C̄ = ⌈5C + 20d log T⌉`,
`ϵ = T⁻³`) whose feedback is corrupted in at most `C` rounds, at the start of every round
`t ≤ T` at most `C̄` of the evidence sets `𝓗_j` are not correct (Definition 3.1 with `ϵ = T⁻³`).

**Formalization Note.** Every tie-breaking choice of the run is allowed (`IsAlg4Run`); the
corruption constraint is evaluated on the run's own prices (`IsCorrupted`). -/
theorem lemma_4_1 (d T C : ℕ) (hd : 1 ≤ d) (θ : EuclideanSpace ℝ (Fin d)) (hθ : θ ∈ Theta d)
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (hu : ∀ t < T, u t ∈ Theta d)
    (hv : ∀ t < T, 0 ≤ inner ℝ θ (u t)) (Y : ℕ → Bool) (r : Run d (2 * cbar d T C + 1))
    (hr : IsAlg4Run T C u Y r) (hY : IsCorrupted T C θ u r.p Y) (t : ℕ) (ht : t ≤ T) :
    {j | ¬ SetCorrect (epsT T) θ (r.H t j)}.ncard ≤ cbar d T C := by sorry

end RobustCtxPricing
