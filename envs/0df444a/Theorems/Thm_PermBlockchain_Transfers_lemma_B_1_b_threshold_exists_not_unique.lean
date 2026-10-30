-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_lemma_B_1_b_threshold_exists_not_unique
-- name    : PermBlockchain.Transfers.lemma_B_1_b_threshold_exists_not_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:46.517476+00:00
-- url     : https://prove2.me/theorems/b8848afd-a675-4f6f-97a7-d0ad63d55790
-- title:
--   Lemma B.1(b): for all sufficiently large $\Delta$ a fee threshold $\phi^*$ exists, and it need not be unique (Example B.1); the consequence for $b_k$ is the milestone on the fee rule
-- statement:
--   Let $h(\phi_k;\phi)$ be the fee gain of Lemma B.1.
--
--   1. For every continuous distribution function $G$ supported on $[0,\infty)$, all $L,h,\gamma$ and every $X=\sum_i\chi_i>0$ there is $\bar\Delta$ such that for every $\Delta>\bar\Delta$ there exists $\phi^*\ge0$ with
--   $$h(\phi^*;\phi^*)=0\quad\text{and}\quad h(\phi_k;\phi^*)\ge0\iff\phi_k\le\phi^*\ \text{ for all }\phi_k\ge0.$$
--   2. Such a $\phi^*$ is not necessarily unique: there are a continuous $G$ supported on $[0,\infty)$, parameters $L\ge0$, $h>0$, $\gamma>0$, $X>0$, and $\Delta$ with $\Delta/2>\max\{2X,q-L-h+\gamma\}$ for every median $q$ of $G$, admitting two distinct thresholds $\phi^*$.
--
--   Example B.1 is a witness for part 2: $\Delta=13/3$, $L=h=1/2$, $\gamma=1$, $X=1$, $G(\phi)=\phi/4$ on $[0,3]$, $\phi-9/4$ on $(3,13/4]$ and $1$ beyond, with thresholds $\phi^*=3$ and $\phi^*=10/3$.
--
--   The lemma's further sentence, "Therefore, $b_k=1$ if and only if $\phi_k\le\phi^*$", is a statement about the game and is the separate milestone on the fee rule.
--
--   Differences from the source:
--   - reading: for all sufficiently large Δ → ∃ Δbar, ∀ Δ > Δbar, with G, L, h, γ, X fixed before Δbar; reason: the paper views L as fixed and lets Δ vary (p. 35)
--   - reading: φ* is not necessarily unique with a general cumulative distribution function G → there exist G, L ≥ 0, h > 0, γ > 0, X > 0 and Δ in the proof's regime with two distinct thresholds; reason: an existence claim, witnessed by Example B.1; the regime condition rules out a degenerate witness
--   - reading: a continuous distribution G that is supported on [0, ∞) (p. 9) → G = cdf ν for a probability measure ν with NullSingletonClass ν and ν (Iio 0) = 0; reason: continuity is the absence of atoms; full support is not meant (Example B.1)
--   - generalization: L ≥ 0, h > l ≥ 0, γ > 0 in part 1 → L, h, γ arbitrary reals; reason: the proof uses no sign condition on them; every instance of the paper is covered
--   - encoding: Therefore, b_k = 1 if and only if φ_k ≤ φ* → stated in the separate milestone proof_prop_4_9_fee_rule_threshold; reason: the clause concerns the consumers' problem (16), not the function h; it is stated there at full strength and the title says so
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), Appendix B, Lemma B.1(b), p. 38 (PDF p. 39); Example B.1, pp. 40–41 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_feeGain

namespace PermBlockchain.Transfers

/-- **Lemma B.1(b): for all sufficiently large `Δ` a fee threshold `φ*` exists, and it need not be unique (Example B.1); the consequence for `b_k` is the milestone `proof_prop_4_9_fee_rule_threshold`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), Appendix B, Lemma B.1(b), p. 38 (PDF p. 39): "For all sufficiently large ∆, there exists
φ* ∈ [0, +∞) such that h(φ*; φ*) = 0 and h(φ_k; φ*) ≥ 0 if and only if φ_k ≤ φ*. Therefore,
b_k = 1 if and only if φ_k ≤ φ*. Moreover, φ* is not necessarily unique with a general cumulative
distribution function G."; Example B.1, pp. 40–41 (PDF pp. 41–42).

1. For every continuous distribution `G = cdf ν` supported on `[0, ∞)`, all real `L, h, γ` and
   every `X = Σχ_i > 0` there is `Δ̄` such that for every `Δ > Δ̄` some `φ* ≥ 0` satisfies
   `h(φ*; φ*) = 0` and `h(φ_k; φ*) ≥ 0 ↔ φ_k ≤ φ*` for all `φ_k ≥ 0`.
2. Non-uniqueness: there are such a `G`, parameters `L ≥ 0`, `h > 0`, `γ > 0`, `X > 0` and `Δ` in
   the regime of the proof (`Δ/2 > max{2X, q − L − h + γ}` for every median `q`) with two distinct
   thresholds `φ*`.

**Formalization Note.** The sentence "Therefore, b_k = 1 if and only if φ_k ≤ φ*" is about the
game and is the separate milestone `proof_prop_4_9_fee_rule_threshold`. Example B.1 (`Δ = 13/3`,
`L = h = 1/2`, `γ = 1`, `Σχ_i = 1`, `G(φ) = φ/4` on `[0, 3]`, `φ − 9/4` on `(3, 13/4]`, `1` beyond;
`φ* = 3` and `φ* = 10/3`) is a witness for part 2. -/
theorem lemma_B_1_b_threshold_exists_not_unique :
    (∀ (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν]
        [MeasureTheory.NullSingletonClass ν], ν (Set.Iio 0) = 0 → ∀ L h γ X : ℝ, 0 < X →
        ∃ Δbar : ℝ, ∀ Δ : ℝ, Δbar < Δ → ∃ φs : ℝ, 0 ≤ φs ∧
          feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φs φs = 0 ∧
          ∀ φk : ℝ, 0 ≤ φk →
            (0 ≤ feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φk φs ↔ φk ≤ φs)) ∧
    (∃ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsProbabilityMeasure ν ∧
        MeasureTheory.NullSingletonClass ν ∧ ν (Set.Iio 0) = 0 ∧
        ∃ L h γ X Δ : ℝ, 0 ≤ L ∧ 0 < h ∧ 0 < γ ∧ 0 < X ∧
          (∀ q : ℝ, ProbabilityTheory.cdf ν q = 1 / 2 → max (2 * X) (q - L - h + γ) < Δ / 2) ∧
          ∃ φ₁ φ₂ : ℝ, φ₁ ≠ φ₂ ∧
            (0 ≤ φ₁ ∧ feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φ₁ φ₁ = 0 ∧
              ∀ φk : ℝ, 0 ≤ φk →
                (0 ≤ feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φk φ₁ ↔ φk ≤ φ₁)) ∧
            (0 ≤ φ₂ ∧ feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φ₂ φ₂ = 0 ∧
              ∀ φk : ℝ, 0 ≤ φk →
                (0 ≤ feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φk φ₂ ↔ φk ≤ φ₂))) := by sorry

end PermBlockchain.Transfers
