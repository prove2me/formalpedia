-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_proof_lemma_B_1_b_ivt_threshold
-- name    : PermBlockchain.Transfers.proof_lemma_B_1_b_ivt_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:15.830998+00:00
-- url     : https://prove2.me/theorems/82c5a923-ad6c-4c29-9e02-7c269ff17029
-- title:
--   Proof of Lemma B.1(b): for $\Delta/2>\max\{2\sum\chi_i,\,G^{-1}(0.5)-L-h+\gamma\}$ a fee threshold $\phi^*$ exists in $(\Delta/2+L+h-\gamma,\,\Delta+L+h-\gamma]$
-- statement:
--   Let $G$ be the distribution function of a continuous probability distribution supported on $[0,\infty)$, let $X=\sum_i\chi_i>0$ and let $q$ be a median, $G(q)=1/2$. With $h(\phi_k;\phi)$ the fee gain of Lemma B.1, suppose
--   $$\frac{\Delta}{2}>\max\bigl\{2X,\ q-L-h+\gamma\bigr\}.$$
--   Then there is
--   $$\phi^*\in\Bigl(\frac{\Delta}{2}+L+h-\gamma,\ \Delta+L+h-\gamma\Bigr]$$
--   with $h(\phi^*;\phi^*)=0$, and for every $\phi_k\ge0$: $h(\phi_k;\phi^*)\ge0$ if and only if $\phi_k\le\phi^*$.
--
--   This is the explicit-threshold form of Lemma B.1(b): it gives the value of $\Delta$ above which the fee mechanism works, and locates $\phi^*$ where the purchase-stage argument needs it.
--
--   Differences from the source:
--   - reading: G⁻¹(0.5) → any q with cdf ν q = 1/2; reason: G is continuous, so such q exist; the statement holds for each of them and so for every quantile convention
--   - reading: a continuous distribution G that is supported on [0, ∞) (p. 9) → G = cdf ν for a probability measure ν with NullSingletonClass ν (no atoms) and ν (Iio 0) = 0; reason: continuity of a distribution function is the absence of atoms; full support is not meant, since Example B.1's G is constant beyond 13/4
--   - generalization: L ≥ 0, h > l ≥ 0, γ > 0 → L, h, γ arbitrary reals; reason: the argument uses only the displayed inequality; every instance of the paper is covered
--   - encoding: Σ_{i∈M} χ_i with χ_i > 0, and h(φ_k; φ) → a real X > 0 and the closed form feeGain; reason: only the sum enters; feeGain is the proof's first display
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), Appendix B, proof of Lemma B.1(b), unnumbered, p. 40 (PDF p. 41)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_feeGain

namespace PermBlockchain.Transfers

/-- **Proof of Lemma B.1(b): for `Δ/2 > max{2Σχ_i, G⁻¹(0.5) − L − h + γ}` a fee threshold `φ*` exists in `(Δ/2 + L + h − γ, Δ + L + h − γ]`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), Appendix B, proof of Lemma B.1(b), unnumbered, p. 40 (PDF p. 41): "This implies that when
∆/2 > max{2 Σ_{i:i∈M} χ_i, G⁻¹(0.5) − L − h + γ}, by intermediate value theorem, there exists a
solution φ* ∈ (∆/2 + L + h − γ, ∆ + L + h − γ] such that h(φ*; φ*) = l(φ*) = 0. With this φ*, we
have that h(φ_k; φ*) ≥ 0 if and only if φ_k ≤ φ*."

Here `G = cdf ν` for a probability measure `ν` on `ℝ` without atoms and with no mass on
`(−∞, 0)` (a continuous distribution supported on `[0, ∞)`, p. 9), `X = Σχ_i > 0`, and `q` is any
median of `G`.

**Formalization Note.** `G⁻¹(0.5)` is read as any `q` with `G q = 1/2`; such `q` exist because
`G` is continuous, so every quantile convention is covered. -/
theorem proof_lemma_B_1_b_ivt_threshold (ν : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure ν] [MeasureTheory.NullSingletonClass ν] (hν : ν (Set.Iio 0) = 0)
    {Δ L h γ X q : ℝ} (hX : 0 < X) (hq : ProbabilityTheory.cdf ν q = 1 / 2)
    (hΔ : max (2 * X) (q - L - h + γ) < Δ / 2) :
    ∃ φs ∈ Set.Ioc (Δ / 2 + L + h - γ) (Δ + L + h - γ),
      feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φs φs = 0 ∧
      ∀ φk : ℝ, 0 ≤ φk →
        (0 ≤ feeGain Δ L h γ X (ProbabilityTheory.cdf ν) φk φs ↔ φk ≤ φs) := by sorry

end PermBlockchain.Transfers
