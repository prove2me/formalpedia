-- Prove2me | Theorems.Thm_PermBlockchain_Transfers_proof_prop_4_9_fee_rule_threshold
-- name    : PermBlockchain.Transfers.proof_prop_4_9_fee_rule_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:21.528353+00:00
-- url     : https://prove2.me/theorems/956d87a1-2745-479e-8f39-dfcec1affd4b
-- title:
--   Proof of Proposition 4.9: paying the fee is optimal exactly for $\phi_k\le\phi^*$
-- statement:
--   In the setting of the fee-stage milestone (all manufacturers adopt, high types price $\gamma$, low types $\max\{\gamma-(h-l),0\}$, $H=L+\Delta$, $\Delta>0$, $l<h$, $\gamma>0$, $m\ge1$, Bayes-consistent beliefs), let $X=\sum_i\chi_i>0$, let $G$ be the distribution function of the outside option, and let
--   $$\phi^*\in\Bigl(\frac{\Delta}{2}+L+h-\gamma,\ \Delta+L+h-\gamma\Bigr],\qquad G(\phi^*)>0,\qquad h(\phi^*;\phi^*)=0.$$
--   With the fee $\kappa=X/G(\phi^*)$, for every consumer type and every outside option $\phi$,
--   $$g(0,\phi)\le g(1,\phi)\iff\phi\le\phi^*.$$
--   Hence "$b_k=1$ if and only if $\phi_k\le\phi^*$" is an optimal fee rule, and every optimal rule agrees with it except possibly at $\phi=\phi^*$.
--
--   Differences from the source:
--   - generalization: b_k = 1 if and only if φ_k ≤ φ* is an optimal decision rule → g(0) ≤ g(1) ↔ φ ≤ φ*, for every real φ; reason: the equivalence implies that the threshold rule is optimal and characterizes all optimal rules up to φ = φ*
--   - generalization: φ* given by Lemma B.1(b); standing m ≥ 2, 0 ≤ L, 0 ≤ l → every φ* in (Δ/2 + L + h − γ, Δ + L + h − γ] with G(φ*) > 0 and h(φ*; φ*) = 0; 1 ≤ m, L and l arbitrary; reason: the threshold of the proof of Lemma B.1(b) has these properties; every instance of the paper is covered
--   - encoding: κ = Σ_i χ_i / G(φ*) → the same, with the hypothesis 0 < G(φ*); reason: excludes only the undefined case (Lean's x / 0 = 0); in the paper G(φ*) ≥ 1/2
--   - encoding: consumer beliefs and information under α = 1/2 (p. 9), with Bayes updating from the uniform prior on assignments with m of each type (p. 12) → every belief system satisfying IsConsistentBelief for paperStrategy, with the deterministic revelation `revealed`; reason: α = 1/2 signals carry no information, so the chain's exact revelation is the whole information structure; the statement holds for every consistent belief system
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, unnumbered, p. 37 (PDF p. 38)

import Mathlib
import Definitions.Def_PermBlockchain_Transfers_IsConsistentBelief
import Definitions.Def_PermBlockchain_Transfers_feeValue
import Definitions.Def_PermBlockchain_Transfers_paperStrategy
import Definitions.Def_PermBlockchain_Transfers_feeGain

namespace PermBlockchain.Transfers

/-- **Proof of Proposition 4.9: paying the fee is optimal exactly for `φ_k ≤ φ*`.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), proof of Proposition 4.9, unnumbered, p. 37 (PDF p. 38): "By Lemma B.1(b) in Appendix B, it
follows that there exists φ* ∈ [0, +∞) such that h(φ*; φ*) = 0 and h(φ_k; φ*) ≥ 0 if and only if
φ_k ≤ φ*. Thus, b_k = 1 if and only if φ_k ≤ φ* is an optimal decision rule for all consumers."

Let `X = Σ_i χ_i > 0`, `G = cdf ν`, and let `φ* ∈ (Δ/2 + L + h − γ, Δ + L + h − γ]` with
`G(φ*) > 0` and `h(φ*; φ*) = 0`. With the fee `κ = X / G(φ*)`, at the on-path history of
`paperStrategy γ h l` and under every consistent belief system, a consumer of either type weakly
prefers paying the fee (`g(0) ≤ g(1)`) if and only if her outside option satisfies `φ ≤ φ*`.

**Formalization Note.** `0 < G(φ*)` excludes only the case where `κ = X / G(φ*)` is undefined
(Lean would give `κ = 0`); in the paper `G(φ*) ≥ 1/2`. The equivalence is stated for every real
`φ`. -/
theorem proof_prop_4_9_fee_rule_threshold {m : ℕ} (hm : 1 ≤ m) {L Δ h l γ : ℝ} (hΔ : 0 < Δ)
    (hlh : l < h) (hγ : 0 < γ) (χ : Mfr m → ℝ) (hX : 0 < ∑ i, χ i)
    (ν : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ν] (φs : ℝ)
    (hφs : φs ∈ Set.Ioc (Δ / 2 + L + h - γ) (Δ + L + h - γ))
    (hG : 0 < ProbabilityTheory.cdf ν φs)
    (hroot : feeGain Δ L h γ (∑ i, χ i) (ProbabilityTheory.cdf ν) φs φs = 0)
    (β : BeliefSystem m) (hβ : IsConsistentBelief (paperStrategy γ h l) β)
    (θ : Mfr m → MType) (hθ : θ ∈ Assignments m) (t : Horiz) (φ : ℝ) :
    feeValue (L + Δ) L h l β ((∑ i, χ i) / ProbabilityTheory.cdf ν φs)
        (histOf (onPath (paperStrategy γ h l) θ)) t φ false ≤
      feeValue (L + Δ) L h l β ((∑ i, χ i) / ProbabilityTheory.cdf ν φs)
        (histOf (onPath (paperStrategy γ h l) θ)) t φ true ↔ φ ≤ φs := by sorry

end PermBlockchain.Transfers
