-- Prove2me | Theorems.Thm_RobustCtxPricing_theorem_4_2
-- name    : RobustCtxPricing.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T23:59:47.009663+00:00
-- url     : https://prove2.me/theorems/dbf0bac7-91eb-41a6-93c1-46501c8bfafc
-- title:
--   Theorem 4.2 — with a known corruption budget, Algorithm 4 has regret $O(Cd+d^2\log T)$
-- statement:
--   There is an absolute constant $K$ such that the following holds. Let $d\ge1$ be the context dimension, $T\ge2$ the horizon and $C\in\mathbb N$ the corruption budget, known to the seller. Let $\theta^\star\in\Theta=\mathcal B_d(0,1)$ and let $u_1,\dots,u_T\in\Theta$ be any contexts with valuations $v_t=\langle\theta^\star,u_t\rangle\ge0$. Run Algorithm 4 with $\epsilon=T^{-3}$ and $\bar C=\lceil5C+20d\log T\rceil$, under any tie-breaking, against feedback $Y_t$ that differs from the true sale bit $\mathbb I\{p_t\le v_t\}$ in at most $C$ rounds. Then
--   $$
--   R_T=\sum_{t=1}^T\big(v_t-p_t\,\mathbb I\{p_t\le v_t\}\big)\le K\,\big(Cd+d^2\log T\big).
--   $$
--   The corruption budget and the horizon enter additively: the regret is linear in $C$ with no $\log T$ factor, and poly-logarithmic in $T$ with no factor of $C$.
--
--   Differences from the source:
--   - reading: R_T = O(Cd + d² log T) → ∃ K absolute, ∀ d ≥ 1, T ≥ 2, C, θ⋆, contexts, feedback and runs: R_T ≤ K(Cd + d² log T); reason: at T = 1 the literal bound K·Cd fails (d = 1, C = 0, θ⋆ = u_1 = e₁: the single round explores at price 0 and R_1 = 1), and the paper's proof uses T ≥ 2 (p.17); at d = 0 every round commits at price −1/(8T), R_T = 1/8 and the bound is 0
--   - generalization: Algorithm 4 (no tie-breaking fixed; Commit "uses the solution to the inequality") → every run under every tie-break: any solution of (3), any non-predicting receiving set, any coefficients satisfying (1); reason: specializes to any fixed rule and to the minimizers
--   - encoding: the adaptive adversary of §2.2 → all context and feedback sequences, with the corruption constraint evaluated on the run's own prices; reason: the run is determined by the contexts, the feedback and the tie-breaking choices
--   - encoding: rounds t = 1, …, T and bits in {0, 1} → rounds 0, …, T − 1 of ℕ-indexed sequences and Bool bits; reason: Lean convention; same instances
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball; reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); the closed ball contains the open one and differs from it by a null set
--   - reading: the budget C, an upper bound on the number of corrupted rounds (its type is not stated) → C ∈ ℕ; reason: it bounds the count |S|
--   - reading: log → the natural logarithm Real.log; reason: the base is not stated; natural log is the standard meaning, and the constants of p.17 hold with it
--   - encoding: the test (1), min_λ {…} ≤ 1/(8T) → ∃ λ with ϵ‖λ‖₁ + ‖u − Σ λ_i u_i‖₂ ≤ 1/(8T); reason: for ϵ > 0 the objective is continuous and coercive, so the minimum is attained and the two tests agree
--   - encoding: evidence sets 𝓗_1, …, 𝓗_{2C̄+1} → lists of samples in insertion order, indexed by Fin (2C̄+1); reason: Lean convention; a repeated sample changes neither the test (1) nor the estimate
--   - encoding: "(C̄ + 1)-st largest lower endpoint" → the entry with index C̄ of the lower endpoints sorted non-increasingly; reason: Lean convention; same instances
--   - encoding: the cases of Update-Density overlap on the hyperplanes ⟨u_t, θ⟩ = m_t ± ϵ/2 → the window case takes priority there; reason: the page leaves the overlap open; for u_t ≠ 0 the hyperplanes are null, and for u_t = 0 a window median of a positive mass has |m_t| < ϵ/2, so they do not meet the update
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Theorem 4.2, p.21 (Algorithm 4, p.21; C̄ and ϵ, §4.1, p.20; model §2, pp.10–11)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Density
import Definitions.Def_RobustCtxPricing_Algorithm4

namespace RobustCtxPricing

/-- **Theorem 4.2.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §4.2, p.21: "Algorithm 4 attains regret: `R_T = O(Cd + d² log T)`."

There is an absolute constant `K` such that for every dimension `d ≥ 1`, horizon `T ≥ 2`,
corruption budget `C ∈ ℕ`, parameter `θ⋆ ∈ Θ`, context sequence `u_1, …, u_T ∈ Θ` with valuations
`v_t = ⟨θ⋆, u_t⟩ ≥ 0`, observed feedback `Y` and run of Algorithm 4 (horizon `T`,
`C̄ = ⌈5C + 20d log T⌉`, `ϵ = T⁻³`, any tie-breaking) whose feedback differs from the true sale bit
`𝕀{p_t ≤ v_t}` in at most `C` rounds, the regret satisfies `R_T ≤ K (Cd + d² log T)`.

**Formalization Note.** `O(·)` is "`∃ K` absolute, quantified before every other variable"; it is
read for `T ≥ 2` (at `T = 1` the literal bound `K·Cd` fails for `C = 0`: `d = 1`, `θ⋆ = 1`,
`u_1 = 1` gives `R_1 = 1`; the paper's proof uses `T ≥ 2`, p.17). The adaptive adversary of §2.2 is
covered by quantifying over all `(u, Y)` and all runs, with the corruption constraint evaluated on
the run's own prices. `log` is natural. -/
theorem theorem_4_2 : ∃ K : ℝ, ∀ (d T C : ℕ), 1 ≤ d → 2 ≤ T →
    ∀ θ : EuclideanSpace ℝ (Fin d), θ ∈ Theta d →
    ∀ u : ℕ → EuclideanSpace ℝ (Fin d), (∀ t < T, u t ∈ Theta d) →
      (∀ t < T, 0 ≤ inner ℝ θ (u t)) →
    ∀ (Y : ℕ → Bool) (r : Run d (2 * cbar d T C + 1)),
      IsAlg4Run T C u Y r → IsCorrupted T C θ u r.p Y →
      regret T θ u r.p ≤ K * ((C : ℝ) * d + (d : ℝ) ^ 2 * Real.log T) := by sorry

end RobustCtxPricing
