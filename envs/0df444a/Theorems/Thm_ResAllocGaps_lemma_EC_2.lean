-- Prove2me | Theorems.Thm_ResAllocGaps_lemma_EC_2
-- name    : ResAllocGaps.lemma_EC_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:07.084198+00:00
-- url     : https://prove2.me/theorems/fc50bf51-7bc2-4e79-a6b0-1763b3186e39
-- title:
--   Lemma EC.2 — loss bound $\frac{\alpha_0}{8}T^{1/2-1/(2(1+\beta))}$ on $\mathcal E^c\cap\mathcal H\cap\mathcal C\cap\mathcal P$ (corrected: $\mathcal P_1,\mathcal P_2$ without lower bounds)
-- statement:
--   Fix $\beta>0$, the law $F_\beta$, $T\ge1$ and $B=\lfloor T/2\rfloor$, and let $\pi\in\Pi(B,T)$ be any feasible online policy. With $A=\mathcal E_\pi^c\cap\mathcal H\cap\mathcal C\cap\mathcal P$,
--   $$\mathbb E\big[\Lambda(B,T;\pi)\,\mathbb 1_A\big]\ \ge\ \frac{\alpha_0}{8}\,T^{\frac12-\frac1{2(1+\beta)}}\ \mathbb P(A),$$
--   where $\alpha_0=(129/128)^{1/(1+\beta)}-1$. When $\mathbb P(A)>0$ this is the paper's bound on $\mathbb E[\Lambda\mid A]$.
--
--   On $A$ the policy has rejected most of the middle window $I_{M_c}$ by time $B$, while the benchmark accepts all of it.
--
--   **Formalization Note** The constant is the printed $\alpha_0/8$. The paper's proof (p.ec9, step (f)) ends with $\alpha_0\ell/8=\alpha_0/32$, which is all the proof of Theorem 1 needs.
--
--   Differences from the source:
--   - correction: P₁ = {√T/256 ≤ N(I_Mp, 1, B) ≤ √T/64}, P₂ = {√T/256 ≤ N(I_Mp, B+1, T) ≤ √T/64} (EC.9), (EC.10) → P₁ = {N(I_Mp, 1, B) ≤ √T/64}, P₂ = {N(I_Mp, B+1, T) ≤ √T/64}; reason: with the printed lower bounds Lemma EC.4 is false: for any β > 0, F = F_β, B = ⌊T/2⌋, N(I_Mp, 1, B) ∼ Bin(⌊T/2⌋, T^{−1/2}/128) has mean at most √T/256, so P(P₁ᶜ) ≥ P(N < mean) → 1/2; no step of the proof uses the lower bounds, so the mission uses one corrected P throughout
--   - generalization: the optimal dynamic programming policy DP → every feasible online policy π ∈ Π(⌊T/2⌋, T); reason: DP is a feasible online policy, so the statement specializes to the page. The printed proof is pathwise and reaches only α₀ℓ/8 = α₀/32 (p.ec9, step (f)) for any policy with at most B acceptances, so it does not prove the printed α₀/8 for DP or for any other policy; no counterexample is known, and the bound at α₀/8 needs a non-pathwise argument (the loss after time B)
--   - encoding: E[Λ | A] ≥ κ → ∫_A Λ dP ≥ κ · P(A); reason: equivalent when P(A) > 0, where the paper's conditional expectation is defined; trivially true when P(A) = 0
--   - encoding: fix the time horizon T > 0 (p.ec1) → T : ℕ with 1 ≤ T; reason: same horizons
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Lemma EC.2, p.ec4 (proof §EC.1.2, pp.ec8–ec9)

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy
import Definitions.Def_ResAllocGaps_muBeta
import Definitions.Def_ResAllocGaps_arrivals

open MeasureTheory

namespace ResAllocGaps

/-- **Lemma EC.2**, Besbes, Kanoria & Kumar, arXiv:2205.09078v2, p.ec4: "Consider the event
`Eᶜ ∩ H ∩ C ∩ P`, then we have that `E[Λ(B, T; DP) | Eᶜ ∩ H ∩ C ∩ P] ≥ (α₀/8) T^{1/2 − 1/(2(1+β))}`,
where `α₀ = (129/128)^{1/(1+β)} − 1` defined in (EC.2)." Here for `β > 0`, the law `F_β`, `T ≥ 1`,
`B = ⌊T/2⌋` and **every** feasible online policy `π` in place of the DP policy, at the printed
constant `α₀/8`.

**Formalization Note.** The conditional expectation is written as `∫_A Λ ≥ κ · P(A)` with
`A = E_πᶜ ∩ H ∩ C ∩ P` (equivalent when `P(A) > 0`, trivial when `P(A) = 0`). `P` is the corrected
event. The paper's proof (p.ec9, step (f)) derives the constant `α₀ℓ/8 = α₀/32`; the printed
`α₀/8` is stated. -/
theorem lemma_EC_2 (β : ℝ) (hβ : 0 < β) (T : ℕ) (hT : 1 ≤ T)
    (π : OnlinePolicy (muBeta β) T (halfBudget T)) :
    alpha0 β / 8 * (T : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (1 + β))) *
        ((sampleLaw (muBeta β) T) ((eventE π β)ᶜ ∩ eventH β T ∩ eventC β T ∩ eventP β T)).toReal ≤
      ∫ ω in (eventE π β)ᶜ ∩ eventH β T ∩ eventC β T ∩ eventP β T, π.loss ω
        ∂(sampleLaw (muBeta β) T) := by sorry

end ResAllocGaps
