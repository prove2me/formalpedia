-- Prove2me | Theorems.Thm_ResAllocGaps_lemma_EC_1
-- name    : ResAllocGaps.lemma_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:05.788212+00:00
-- url     : https://prove2.me/theorems/6be595be-1f8c-4ccf-88cf-4099087fdb93
-- title:
--   Lemma EC.1 — loss bound $\frac{\alpha_0\ell}{32}T^{1/2-1/(2(1+\beta))}$ on $\mathcal E\cap\tilde{\mathcal H}\cap\mathcal C\cap\mathcal P$ (corrected: $\mathcal P_1,\mathcal P_2$ without lower bounds)
-- statement:
--   Fix $\beta>0$, the law $F_\beta$, $T\ge1$ and $B=\lfloor T/2\rfloor$, and let $\pi\in\Pi(B,T)$ be any feasible online policy. With $A=\mathcal E_\pi\cap\tilde{\mathcal H}\cap\mathcal C\cap\mathcal P$,
--   $$\mathbb E\big[\Lambda(B,T;\pi)\,\mathbb 1_A\big]\ \ge\ \frac{\alpha_0\ell}{32}\,T^{\frac12-\frac1{2(1+\beta)}}\ \mathbb P(A),$$
--   where $\alpha_0=(129/128)^{1/(1+\beta)}-1$ and $\ell=\tfrac14$. When $\mathbb P(A)>0$ this is the paper's bound on the conditional expectation $\mathbb E[\Lambda\mid A]$.
--
--   On $A$ the policy has spent part of its budget on the middle window $I_{M_c}$ while the benchmark fills its whole budget from $I_H$; each such acceptance costs at least $\alpha_0\Delta_\beta$.
--
--   Differences from the source:
--   - correction: P₁ = {√T/256 ≤ N(I_Mp, 1, B) ≤ √T/64}, P₂ = {√T/256 ≤ N(I_Mp, B+1, T) ≤ √T/64} (EC.9), (EC.10) → P₁ = {N(I_Mp, 1, B) ≤ √T/64}, P₂ = {N(I_Mp, B+1, T) ≤ √T/64}; reason: with the printed lower bounds Lemma EC.4 is false: for any β > 0, F = F_β, B = ⌊T/2⌋, N(I_Mp, 1, B) ∼ Bin(⌊T/2⌋, T^{−1/2}/128) has mean at most √T/256, so P(P₁ᶜ) ≥ P(N < mean) → 1/2; no step of the proof uses the lower bounds, so the mission uses one corrected P throughout
--   - generalization: the optimal dynamic programming policy DP → every feasible online policy π ∈ Π(⌊T/2⌋, T); reason: DP is a feasible online policy, so the statement specializes to the page; the proof uses only that π is online and accepts at most B candidates
--   - encoding: E[Λ | A] ≥ κ → ∫_A Λ dP ≥ κ · P(A); reason: equivalent when P(A) > 0, where the paper's conditional expectation is defined; trivially true when P(A) = 0
--   - encoding: fix the time horizon T > 0 (p.ec1) → T : ℕ with 1 ≤ T; reason: same horizons
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Lemma EC.1, p.ec4 (proof §EC.1.1, pp.ec6–ec7)

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy
import Definitions.Def_ResAllocGaps_muBeta
import Definitions.Def_ResAllocGaps_arrivals

open MeasureTheory

namespace ResAllocGaps

/-- **Lemma EC.1**, Besbes, Kanoria & Kumar, arXiv:2205.09078v2, p.ec4: "Consider the event
`E ∩ H̃ ∩ C ∩ P`, then we have that `E[Λ(B, T; DP) | E ∩ H̃ ∩ C ∩ P] ≥ (α₀ℓ/32) T^{1/2 − 1/(2(1+β))}`,
where `α₀ = (129/128)^{1/(1+β)} − 1` defined in (EC.2) and `ℓ = 1/2 − g/2`." Here for `β > 0`, the
law `F_β`, `T ≥ 1`, `B = ⌊T/2⌋` and **every** feasible online policy `π` in place of the DP policy.

**Formalization Note.** The conditional expectation is written as
`∫_A Λ ≥ κ · P(A)` with `A = E_π ∩ H̃ ∩ C ∩ P`, which is equivalent when `P(A) > 0` (where the
paper's conditional expectation is defined) and trivial when `P(A) = 0`. `P` is the corrected
event. `ℓ = 1/4` (`gapLo`). -/
theorem lemma_EC_1 (β : ℝ) (hβ : 0 < β) (T : ℕ) (hT : 1 ≤ T)
    (π : OnlinePolicy (muBeta β) T (halfBudget T)) :
    alpha0 β * gapLo / 32 * (T : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (1 + β))) *
        ((sampleLaw (muBeta β) T) (eventE π β ∩ eventHt β T ∩ eventC β T ∩ eventP β T)).toReal ≤
      ∫ ω in eventE π β ∩ eventHt β T ∩ eventC β T ∩ eventP β T, π.loss ω
        ∂(sampleLaw (muBeta β) T) := by sorry

end ResAllocGaps
