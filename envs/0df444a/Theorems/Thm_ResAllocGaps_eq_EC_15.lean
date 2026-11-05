-- Prove2me | Theorems.Thm_ResAllocGaps_eq_EC_15
-- name    : ResAllocGaps.eq_EC_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:17.6092+00:00
-- url     : https://prove2.me/theorems/a76ae313-7905-4146-8ae7-c394f1699073
-- title:
--   (EC.15) — the two error events have probability at least a product of block probabilities (corrected: $\mathcal P_1,\mathcal P_2$ without lower bounds)
-- statement:
--   Fix $\beta>0$, the law $F_\beta$, $T\ge1$ and $B=\lfloor T/2\rfloor$, and let $\pi\in\Pi(B,T)$ be any feasible online policy. Then the block factorization
--   $$\mathbb P(\mathcal E_\pi\cap\tilde{\mathcal H}\cap\mathcal C\cap\mathcal P)+\mathbb P(\mathcal E_\pi^c\cap\mathcal H\cap\mathcal C\cap\mathcal P)=\mathbb P(\mathcal E_\pi\cap\mathcal H_1\cap\mathcal C_1\cap\mathcal P_1)\,\mathbb P(\tilde{\mathcal H}_2\cap\mathcal C_2\cap\mathcal P_2)+\mathbb P(\mathcal E_\pi^c\cap\mathcal H_1\cap\mathcal C_1\cap\mathcal P_1)\,\mathbb P(\mathcal H_2\cap\mathcal C_2\cap\mathcal P_2)$$
--   holds, and
--   $$\mathbb P(\mathcal E_\pi\cap\tilde{\mathcal H}\cap\mathcal C\cap\mathcal P)+\mathbb P(\mathcal E_\pi^c\cap\mathcal H\cap\mathcal C\cap\mathcal P)\ \ge\ \min\big\{\mathbb P(\tilde{\mathcal H}_2\cap\mathcal C_2\cap\mathcal P_2),\ \mathbb P(\mathcal H_2\cap\mathcal C_2\cap\mathcal P_2)\big\}\cdot\mathbb P(\mathcal H_1\cap\mathcal C_1\cap\mathcal P_1).$$
--   The left side is the probability that the policy is on the wrong side of the benchmark's decision; the bound holds because whatever the policy does by time $B$ is independent of the arrivals after $B$.
--
--   **Formalization Note** Probabilities are values in $[0,\infty]$; the two conjuncts are steps (a), (b) and steps (c), (d) of the paper's chain (EC.15).
--
--   Differences from the source:
--   - correction: P₁ = {√T/256 ≤ N(I_Mp, 1, B) ≤ √T/64}, P₂ = {√T/256 ≤ N(I_Mp, B+1, T) ≤ √T/64} (EC.9), (EC.10) → P₁ = {N(I_Mp, 1, B) ≤ √T/64}, P₂ = {N(I_Mp, B+1, T) ≤ √T/64}; reason: with the printed lower bounds Lemma EC.4 is false: for any β > 0, F = F_β, B = ⌊T/2⌋, N(I_Mp, 1, B) ∼ Bin(⌊T/2⌋, T^{−1/2}/128) has mean at most √T/256, so P(P₁ᶜ) ≥ P(N < mean) → 1/2; no step of the proof uses the lower bounds, so the mission uses one corrected P throughout
--   - generalization: the optimal dynamic programming policy DP → every feasible online policy π ∈ Π(⌊T/2⌋, T); reason: DP is a feasible online policy, so the statement specializes to the page; the proof uses only that π is online and accepts at most B candidates
--   - encoding: fix the time horizon T > 0 (p.ec1) → T : ℕ with 1 ≤ T; reason: same horizons
--   - encoding: the chain (a)–(d) of (EC.15) → the identity of (a), (b) and the inequality of (c), (d) as two conjuncts; reason: (a) is the definition of H, H̃, C, P up to associativity of ∩, and the intermediate line (c) is the step from (b) to (d); same content
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Proof of Theorem 1, display (EC.15), p.ec5

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy
import Definitions.Def_ResAllocGaps_muBeta
import Definitions.Def_ResAllocGaps_arrivals

open MeasureTheory

namespace ResAllocGaps

/-- **Display (EC.15)**, Proof of Theorem 1, Besbes, Kanoria & Kumar, arXiv:2205.09078v2, p.ec5, for
`β > 0`, the law `F_β`, `T ≥ 1`, `B = ⌊T/2⌋` and **every** feasible online policy `π` in place of the
DP policy: the block factorization of steps (a), (b),
`P(E ∩ H̃ ∩ C ∩ P) + P(Eᶜ ∩ H ∩ C ∩ P) = P(E ∩ H₁ ∩ C₁ ∩ P₁) P(H̃₂ ∩ C₂ ∩ P₂) + P(Eᶜ ∩ H₁ ∩ C₁ ∩ P₁) P(H₂ ∩ C₂ ∩ P₂)`,
and the bound of steps (c), (d),
`P(E ∩ H̃ ∩ C ∩ P) + P(Eᶜ ∩ H ∩ C ∩ P) ≥ min{P(H̃₂ ∩ C₂ ∩ P₂), P(H₂ ∩ C₂ ∩ P₂)} · P(H₁ ∩ C₁ ∩ P₁)`.

**Formalization Note.** Probabilities are values in `ℝ≥0∞` of `sampleLaw (muBeta β) T`. `P`, `P₁`,
`P₂` are the corrected events. The event `E_π` reads the abilities and seeds of times `1, …, B`. -/
theorem eq_EC_15 (β : ℝ) (hβ : 0 < β) (T : ℕ) (hT : 1 ≤ T)
    (π : OnlinePolicy (muBeta β) T (halfBudget T)) :
    (sampleLaw (muBeta β) T) (eventE π β ∩ eventHt β T ∩ eventC β T ∩ eventP β T) +
          (sampleLaw (muBeta β) T) ((eventE π β)ᶜ ∩ eventH β T ∩ eventC β T ∩ eventP β T) =
        (sampleLaw (muBeta β) T) (eventE π β ∩ eventH1 β T ∩ eventC1 β T ∩ eventP1 β T) *
            (sampleLaw (muBeta β) T) (eventH2t β T ∩ eventC2 β T ∩ eventP2 β T) +
          (sampleLaw (muBeta β) T) ((eventE π β)ᶜ ∩ eventH1 β T ∩ eventC1 β T ∩ eventP1 β T) *
            (sampleLaw (muBeta β) T) (eventH2 β T ∩ eventC2 β T ∩ eventP2 β T) ∧
      min ((sampleLaw (muBeta β) T) (eventH2t β T ∩ eventC2 β T ∩ eventP2 β T))
            ((sampleLaw (muBeta β) T) (eventH2 β T ∩ eventC2 β T ∩ eventP2 β T)) *
          (sampleLaw (muBeta β) T) (eventH1 β T ∩ eventC1 β T ∩ eventP1 β T) ≤
        (sampleLaw (muBeta β) T) (eventE π β ∩ eventHt β T ∩ eventC β T ∩ eventP β T) +
          (sampleLaw (muBeta β) T) ((eventE π β)ᶜ ∩ eventH β T ∩ eventC β T ∩ eventP β T) := by sorry

end ResAllocGaps
