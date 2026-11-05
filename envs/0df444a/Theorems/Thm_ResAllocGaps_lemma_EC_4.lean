-- Prove2me | Theorems.Thm_ResAllocGaps_lemma_EC_4
-- name    : ResAllocGaps.lemma_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:08.676205+00:00
-- url     : https://prove2.me/theorems/e0313414-9d8e-4c48-9f07-2b206214d199
-- title:
--   Lemma EC.4 — $\mathbb P(\mathcal C_1^c),\mathbb P(\mathcal C_2^c),\mathbb P(\mathcal P_1^c),\mathbb P(\mathcal P_2^c)\to0$ (corrected: $\mathcal P_1,\mathcal P_2$ without lower bounds)
-- statement:
--   For every $\eta>0$ there is a horizon $T_0$ such that for every $\beta>0$ and every $T\ge T_0$, under the law $F_\beta$ with $B=\lfloor T/2\rfloor$,
--   $$\mathbb P(\mathcal C_1^c),\ \mathbb P(\mathcal C_2^c),\ \mathbb P(\mathcal P_1^c),\ \mathbb P(\mathcal P_2^c)\ \le\ \eta,$$
--   with the corrected events $\mathcal P_1=\{N(I_{M_p},1,B)\le\sqrt T/64\}$, $\mathcal P_2=\{N(I_{M_p},B+1,T)\le\sqrt T/64\}$. The windows $I_{M_c}$ and $I_{M_p}$ have masses $T^{-1/2}$ and $T^{-1/2}/128$ for every $\beta$, so the counts concentrate around $\sqrt T/2$ and $\sqrt T/256$.
--
--   Differences from the source:
--   - correction: P₁ = {√T/256 ≤ N(I_Mp, 1, B) ≤ √T/64}, P₂ = {√T/256 ≤ N(I_Mp, B+1, T) ≤ √T/64} (EC.9), (EC.10) → P₁ = {N(I_Mp, 1, B) ≤ √T/64}, P₂ = {N(I_Mp, B+1, T) ≤ √T/64}; reason: with the printed lower bounds Lemma EC.4 is false: for any β > 0, F = F_β, B = ⌊T/2⌋, N(I_Mp, 1, B) ∼ Bin(⌊T/2⌋, T^{−1/2}/128) has mean at most √T/256, so P(P₁ᶜ) ≥ P(N < mean) → 1/2; no step of the proof uses the lower bounds, so the mission uses one corrected P throughout
--   - generalization: ≤ 0.001 → ≤ η for every η > 0; reason: η = 0.001 is the page; the proof of Theorem 1 needs the complements below p/2 with the corrected p of Lemma EC.3
--   - generalization: β > 0 fixed, then T₀ → T₀ chosen before β, uniform over β > 0; reason: the window masses do not depend on β, so this specializes to each fixed β
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Lemma EC.4, p.ec6 (proof §EC.1.4, p.ec10)

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy
import Definitions.Def_ResAllocGaps_muBeta
import Definitions.Def_ResAllocGaps_arrivals

open MeasureTheory

namespace ResAllocGaps

/-- **Lemma EC.4** (corrected), Besbes, Kanoria & Kumar, arXiv:2205.09078v2, p.ec6: "There exists
`T₀ < ∞` such that for all `T ≥ T₀`, we have that `P(C₁ᶜ), P(C₂ᶜ), P(P₁ᶜ), P(P₂ᶜ) ≤ 0.001`", with
the corrected events `P₁ = {N(I_{Mp}, 1, B) ≤ √T/64}`, `P₂ = {N(I_{Mp}, B + 1, T) ≤ √T/64}`, for
every bound `η > 0` in place of `0.001`, and `T₀` uniform over `β > 0`.

**Formalization Note (correction).** With the printed lower bound `√T/256 ≤ N(I_{Mp}, ·)` of (EC.9),
(EC.10), the lemma is false: `N(I_{Mp}, 1, B) ∼ Bin(⌊T/2⌋, T^{−1/2}/128)` has mean at most `√T/256`,
so `P(P₁ᶜ) → 1/2`. The lower bounds are used nowhere in the proof. The masses of `I_{Mc}`
(`T^{−1/2}`) and `I_{Mp}` (`T^{−1/2}/128`) do not depend on `β`. -/
theorem lemma_EC_4 :
    ∀ η : ℝ, 0 < η → ∃ T₀ : ℕ, ∀ β : ℝ, 0 < β → ∀ T ≥ T₀,
      ((sampleLaw (muBeta β) T) (eventC1 β T)ᶜ).toReal ≤ η ∧
      ((sampleLaw (muBeta β) T) (eventC2 β T)ᶜ).toReal ≤ η ∧
      ((sampleLaw (muBeta β) T) (eventP1 β T)ᶜ).toReal ≤ η ∧
      ((sampleLaw (muBeta β) T) (eventP2 β T)ᶜ).toReal ≤ η := by sorry

end ResAllocGaps
