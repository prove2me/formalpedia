-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_theorem_3_1
-- name    : PrefixMixLearn.Proper.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:27.723502+00:00
-- url     : https://prove2.me/theorems/417c5870-a76f-432e-9c28-e79de24a55b5
-- title:
--   Theorem 3.1 — proper two-product reconstruction without separation: error (1+θ)κ(α)^{-20}·OPT^(2)_α(P) + ε
-- statement:
--   There is one fair-coin program with access to the prefix-conditional oracle $\mathrm{COND}_P$, and one exponent $c$ fixed before every input, such that for every integer $T\ge1$, all rationals $\alpha\in(0,1/2)$, $\theta\in(0,1]$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$ and every full-support law $P$ on $\{0,1\}^T$, given $(T,\alpha,\theta,\varepsilon,\delta)$:
--   - on every run (every coin and every oracle reply) the program halts within log-cost $(T+\lceil1/\alpha\rceil+\lceil1/\theta\rceil+\lceil1/\varepsilon\rceil+\lceil\log(1/\delta)\rceil+\text{input length}+2)^c$, which bounds its oracle calls, written and returned symbols, random bits, bit time and output length;
--   - on every run its output is a proper balanced dyadic mixture $\hat M\in\mathcal M_{2,\alpha,T}$;
--   - $$\Pr\Big[d_{TV}(P,\hat M)\le(1+\theta)\,\kappa(\alpha)^{-20}\,\mathrm{OPT}^{(2)}_\alpha(P)+\varepsilon\Big]\ge1-\delta,$$
--   where $C_{gen}(\alpha)=\kappa(\alpha)^{-20}$ with $\kappa$ the explicit ledger constant (H.1). No misspecification bound, component parameters, separation or minimum weight is supplied; repeated components and endpoint weights are covered. This is the paper's main learning theorem: agnostic, proper, polynomial-time learning of balanced two-product mixtures from prefix-conditional samples.
--
--   Differences from the source:
--   - reading: bounded by a universal polynomial in T, α⁻¹, θ⁻¹, ε⁻¹, log(1/δ) and rational input encoding lengths → ∃ c before all inputs: log-cost ≤ (T + ⌈1/α⌉ + ⌈1/θ⌉ + ⌈1/ε⌉ + ⌈log(1/δ)⌉ + encLen input + 2)^c on every run, with halting by then; reason: a universal polynomial is dominated by such a power of its arguments; log-cost bounds every listed resource
--   - encoding: a proper balanced dyadic mixture M̂ ∈ M_{2,α,T} → output [B, k⁰, k¹, j] with B ≥ 1, j ≤ 2^B, both k^b 2^{-B} ∈ [α,1−α]^T; M̂ is its law; reason: Appendix B.1 representation
--   - encoding: inputs T, α, θ, ε, δ (rationals) → input [T, num α, den α, num θ, den θ, num ε, den ε, num δ, den δ]; reason: binary numerator/denominator pairs; input length = total bit length
--   - encoding: C_gen(α) = κ^{-20}, κ the computable constant in (H.1) → kappa α ^ (-20) with `kappa` the explicit ledger function; reason: same constant
--   - encoding: "a prefix-conditional algorithm" (no machine is named; costs include bit operations, query writing, response processing, random bits, output length, input reading; learner randomness is fair bits) → a program of the fair-coin log-cost RAM `Machine` (instructions charged by bit lengths; `coin` draws one fair bit; `query` sends a 0/1 prefix to `condOracle P` and is charged for every cell read and written; `halt` for every output cell); a run's law is over the coins and the oracle replies; reason: the paper's model made explicit; one log-cost bound bounds every listed resource (calls, written and returned symbols, coins, bit time, output length)
--   - encoding: COND_P accepts prefixes with 0 ≤ |h| < T (Definition 2.1) → `condOracle P` answers a 0/1 list h with |h| < T (and positive mass) by a fresh suffix with law P_h; every other query gets the empty reply; reason: the paper never issues such queries; the empty reply carries no information about P
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 4 (PDF 6), Theorem 3.1, (3.1)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Ledger
import Definitions.Def_PrefixMixLearn_Proper_Machine

namespace PrefixMixLearn.Proper

/-- Theorem 3.1 (proper two-product reconstruction without separation): one fair-coin program with
prefix-conditional access to `P` and one exponent `c`, fixed before every input, such that for every
`T ≥ 1`, rationals `α ∈ (0, 1/2)`, `θ ∈ (0, 1]`, `ε ∈ (0, 1]`, `δ ∈ (0, 1)` and every full-support
law `P` on `{0,1}^T`: on every run the program halts within log-cost
`(T + ⌈1/α⌉ + ⌈1/θ⌉ + ⌈1/ε⌉ + ⌈log(1/δ)⌉ + input length + 2)^c`, its output is a proper balanced
dyadic two-product mixture `M̂ ∈ M_{2,α,T}`, and
`Pr[d_TV(P, M̂) ≤ (1 + θ) κ(α)^{-20} OPT^(2)_α(P) + ε] ≥ 1 − δ` (3.1). -/
theorem theorem_3_1 :
    ∃ (prog : Program) (c : ℕ),
      ∀ (T : ℕ), 1 ≤ T → ∀ (α θ ε δ : ℚ), 0 < α → α < 1 / 2 → 0 < θ → θ ≤ 1 → 0 < ε → ε ≤ 1 →
        0 < δ → δ < 1 →
      ∀ (P : Cube T → ℝ), IsLaw P → FullSupport P →
        HaltsWithin prog (condOracle P) (learnerInput T α θ ε δ)
          (((T + ⌈1 / α⌉₊ + ⌈1 / θ⌉₊ + ⌈1 / ε⌉₊ + ⌈Real.log (1 / (δ : ℝ))⌉₊ +
            encLen (learnerInput T α θ ε δ) + 2 : ℕ) : ℝ) ^ c) ∧
        OutputsSatisfy prog (condOracle P) (learnerInput T α θ ε δ)
          (fun o => ∃ M : MixCode T, o = encMix M ∧ IsProperMixCode α M) ∧
        1 - (δ : ℝ) ≤ outProb prog (condOracle P) (learnerInput T α θ ε δ)
          (fun o => ∃ M : MixCode T, o = encMix M ∧
            tv P (mixOfCode M) ≤ (1 + θ) * kappa α ^ (-20 : ℤ) * OPT2 α P + ε) := by sorry

end PrefixMixLearn.Proper
