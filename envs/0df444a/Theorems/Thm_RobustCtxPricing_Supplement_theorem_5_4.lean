-- Prove2me | Theorems.Thm_RobustCtxPricing_Supplement_theorem_5_4
-- name    : RobustCtxPricing.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:05:39.717499+00:00
-- url     : https://prove2.me/theorems/73707e58-c8ee-4d03-a463-86596ad628c6
-- title:
--   Theorem 5.4 — with an unknown budget, Algorithm 5 has regret $O(Cd+d^2\log T+d\log T\log(T/\delta))$ with probability $1-\delta$
-- statement:
--   There is an absolute constant $K$ such that the following holds. Let $d\ge1$, $T\ge2$, $C\in\mathbb N$, $\delta\in(0,1)$ and $\theta^\star\in\Theta=\mathcal B_d(0,1)$. Run Algorithm 5 with horizon $T$ and confidence $\delta$ (it is not given $C$), with i.i.d. uniform coins, against any adaptive adversary of the unknown-$C$ model of §2.2 — contexts $u_t\in\Theta$ with $v_t=\langle\theta^\star,u_t\rangle\ge0$ chosen from the history, the decision to corrupt round $t$ taken from the history and $u_t$ before the coin of round $t$ is drawn, corrupted feedback chosen after seeing the price, and at most $C$ corrupted rounds on every realization — and under any tie-breaking rule that is a function of the history. Then, with probability at least $1-\delta$ over the coins,
--   $$
--   R_T\le K\Big(Cd+d^2\log T+d\log T\,\log\frac T\delta\Big).
--   $$
--   Not knowing $C$ costs only the last term: the dependence on $C$ and on $T$ stays decoupled, at the price of an extra $\log(T/\delta)$ factor on $d\log T$.
--
--   Differences from the source:
--   - reading: R_T = O(Cd + d² log T + d log T log(T/δ)) with probability at least 1 − δ → ∃ K absolute, ∀ d ≥ 1, T ≥ 2, C, δ ∈ (0,1), θ⋆, adversary and tie-break: P(R_T > K(Cd + d² log T + d log T · log(T/δ))) ≤ δ; reason: K independent of δ, d, T, C; at T = 1 the log terms vanish and the bound fails as for Theorem 4.2
--   - encoding: "Post U_t with probability q_t and L_t otherwise" → coins ξ_t i.i.d. uniform on [0,1]; post U_t iff ξ_t < q_t; reason: same law of the posted prices
--   - encoding: the unknown-C adaptive adversary of §2.2 and the (unspecified) tie-breaking → executions indexed by the coin sequence, in which contexts, corruption decisions and tie-breaks of round t are equal whenever the histories before t are equal, and Y_t whenever moreover p_t is equal; reason: this is exactly a deterministic adversary strategy and tie-break rule as functions of the history; a randomized adversary independent of the coins is a mixture of deterministic ones
--   - generalization: Algorithm 5 (no tie-breaking fixed) → every tie-break that is a function of the history (any solution of (3), any coefficients satisfying (1)); reason: specializes to any fixed rule
--   - encoding: "with probability at least 1 − δ" → the coin law of the bad event {R_T > bound} is at most δ (outer measure, no measurability assumption); reason: every execution is determined by finitely many comparisons ξ_t < q_t, so the event is measurable and its outer measure is its probability
--   - encoding: M_t ∈ ℝ^{(d+1)×(d+1)}, a_t ∈ ℝ^{d+1}, M_t⁻¹ → Matrix (Fin (d+1)) (Fin (d+1)) ℝ, Fin (d+1) → ℝ, Mathlib's matrix inverse; reason: M_t is positive definite along a run, so the inverse is the true one
--   - encoding: Fail iff (p_t = L_t and Y_t = 0) or (p_t = U_t and Y_t = 1) → Fail iff (the lower price was chosen and Y_t = 0) or (the upper price was chosen and Y_t = 1); reason: L_t ≤ ṽ_t < U_t, so p_t = L_t exactly when the lower price was chosen
--   - encoding: rounds t = 1, …, T and bits in {0, 1} → rounds 0, …, T − 1 of ℕ-indexed sequences and Bool bits; reason: Lean convention; same instances
--   - reading: 𝓑_d(0,1), "the d-dimensional Euclidean ball" → the closed unit ball of EuclideanSpace ℝ (Fin d); reason: the analysis uses ‖u_t‖₂ ≤ 1 and ‖θ⋆‖₂ ≤ 1 (pp.18, 21); this is the published base model's convention
--   - reading: the budget C (its type is not stated) → C ∈ ℕ; reason: it bounds the number |S| of corrupted rounds
--   - reading: log → the natural logarithm Real.log; reason: the base is not stated; natural log is the standard meaning and the constants of the proofs hold with it
--   - encoding: the test (1), min_λ {…} ≤ 1/(8T) → ∃ λ with ϵ‖λ‖₁ + ‖u − Σ λ_i u_i‖₂ ≤ 1/(8T) (published Predicts); reason: for ϵ > 0 the objective is continuous and coercive, so the minimum is attained and the two tests agree
--   - encoding: the cases of Update-Density overlap on the hyperplanes ⟨u_t, θ⟩ = m_t ± ϵ/2 → the window case takes priority there (published updateDensity); reason: the page leaves the overlap open; for u_t ≠ 0 the hyperplanes are Lebesgue-null
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, Theorem 5.4, p.30 (Algorithm 5, p.24; Equations (4)–(10), pp.23–26; unknown-C adversary, §2.2, p.11)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Density
import Definitions.Def_RobustCtxPricing_Algorithm4
import Definitions.Def_RobustCtxPricing_Supplement_Algorithm5
import Definitions.Def_RobustCtxPricing_Supplement_UnknownC

open MeasureTheory

namespace RobustCtxPricing.Supplement

/-- **Theorem 5.4.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual
Pricing*, arXiv:2607.11210, §5.5, p.30: "Let `δ ∈ (0, 1)`, Algorithm 5 guarantees, with probability
at least `1 − δ`: `R_T = O(Cd + d² log T + d log T log(T/δ))`."

There is an absolute constant `K` such that for every dimension `d ≥ 1`, horizon `T ≥ 2`,
corruption budget `C ∈ ℕ` (not given to the algorithm), confidence `δ ∈ (0,1)` and parameter
`θ⋆ ∈ Θ`, and for every unknown-`C` adaptive adversary and tie-breaking rule — given as executions
indexed by the learner's coin sequence `ξ ∈ [0,1]^ℕ`: contexts `u ξ t ∈ Θ` with `⟨θ⋆, u ξ t⟩ ≥ 0`,
corrupted sets `S ξ` with `|S ξ| ≤ C`, feedback `Y ξ` and runs `r ξ` of Algorithm 5 with coins `ξ`,
satisfying `IsUnknownCInteraction` — the probability, over i.i.d. uniform coins, that
`R_T > K (Cd + d² log T + d log T · log(T/δ))` is at most `δ`.

**Formalization Note.** `O(·)` is "`∃ K` absolute, quantified before `d, T, C, δ`"; it is read
for `T ≥ 2`. The probability is `coinLaw` applied to the bad event; measures are outer measures,
so no measurability of the adversary's or the tie-breaking maps is assumed. `log` is natural. -/
theorem theorem_5_4 : ∃ K : ℝ, ∀ (d T C : ℕ) (δ : ℝ), 1 ≤ d → 2 ≤ T → 0 < δ → δ < 1 →
    ∀ θ : EuclideanSpace ℝ (Fin d), θ ∈ Theta d →
    ∀ (u : (ℕ → unitInterval) → ℕ → EuclideanSpace ℝ (Fin d)) (S : (ℕ → unitInterval) → Finset ℕ)
      (Y : (ℕ → unitInterval) → ℕ → Bool) (r : (ℕ → unitInterval) → Run5 d),
      (∀ ξ, ∀ t < T, u ξ t ∈ Theta d ∧ 0 ≤ inner ℝ θ (u ξ t)) →
      (∀ ξ, IsAlg5Run T δ (u ξ) (Y ξ) (fun t => (ξ t : ℝ)) (r ξ)) →
      IsUnknownCInteraction T C θ u S Y (fun ξ => (r ξ).w) (fun ξ => (r ξ).p) →
      coinLaw {ξ | K * ((C : ℝ) * d + (d : ℝ) ^ 2 * Real.log T +
          (d : ℝ) * Real.log T * Real.log (T / δ)) < regret T θ (u ξ) (r ξ).p}
        ≤ ENNReal.ofReal δ := by sorry

end RobustCtxPricing.Supplement
