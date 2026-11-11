-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_corollary_4_1
-- name    : PrefixMixLearn.Proper.corollary_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:46:13.788779+00:00
-- url     : https://prove2.me/theorems/20088917-f428-478f-b368-ea5884b1ed92
-- title:
--   Corollary 4.1 — direct proper agnostic learner for one balanced product, factor 1 + 4/√u
-- statement:
--   There is one fair-coin program with prefix-conditional access and one exponent $c$ such that for every $T\ge1$, rational $\alpha\in(0,1/2)$ ($u=\alpha(1-\alpha)$), rational $0<\varepsilon\le1$, $0<\delta<1$ and full-support $P$ on $\{0,1\}^T$: on every run it halts within log-cost $(T+\lceil1/\alpha\rceil+\lceil1/\varepsilon\rceil+\lceil\log(1/\delta)\rceil+\text{input length}+2)^c$, returns a dyadic balanced product $\hat Q$, and
--   $$\Pr\Big[d_{TV}(P,\hat Q)\le\Big(1+\frac4{\sqrt u}\Big)\mathrm{OPT}_\alpha(P)+\varepsilon\Big]\ge1-\delta.$$
--   It receives no approximation-error bound. For each fixed $\alpha$, with $S=T+1$ and $L=\log(64S/(\varepsilon\delta))$, its target-call count is $O_\alpha(S^5\varepsilon^{-6}L^2)$ on every run. This is the single-product showcase of the trajectory argument and fresh selection.
--
--   Differences from the source:
--   - reading: all resources have a universal polynomial bound in T, α⁻¹, ε⁻¹, log(1/δ) and rational input length → one exponent c, fixed before every input: log-cost ≤ (T + ⌈1/α⌉ + ⌈1/ε⌉ + ⌈log(1/δ)⌉ + encLen input + 2)^c on every run, with halting by then; reason: a universal polynomial is dominated by such a power; log-cost bounds every listed resource
--   - encoding: standalone target-call count O_α(S⁵ε⁻⁶L²) → ∀ α, ∃ C, every run makes at most C (T+1)⁵ ε⁻⁶ log(64(T+1)/(εδ))² calls; reason: O_α: the constant may depend on α only
--   - encoding: a dyadic balanced product Q̂ → output [B, k_1, …, k_T] with B ≥ 1 and every k_i 2^{-B} ∈ [α, 1−α]; reason: Appendix B.1 representation
--   - encoding: "a prefix-conditional algorithm" (no machine is named; costs include bit operations, query writing, response processing, random bits, output length, input reading; learner randomness is fair bits) → a program of the fair-coin log-cost RAM `Machine` (instructions charged by bit lengths; `coin` draws one fair bit; `query` sends a 0/1 prefix to `condOracle P` and is charged for every cell read and written; `halt` for every output cell); a run's law is over the coins and the oracle replies; reason: the paper's model made explicit; one log-cost bound bounds every listed resource (calls, written and returned symbols, coins, bit time, output length)
--   - encoding: COND_P accepts prefixes with 0 ≤ |h| < T (Definition 2.1) → `condOracle P` answers a 0/1 list h with |h| < T (and positive mass) by a fresh suffix with law P_h; every other query gets the empty reply; reason: the paper never issues such queries; the empty reply carries no information about P
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 5 (PDF 7), Corollary 4.1, (4.1)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Machine

namespace PrefixMixLearn.Proper

/-- Corollary 4.1 (direct reconstruction of a balanced product): one fair-coin program with
prefix-conditional access which, for every `T ≥ 1`, rational `α ∈ (0, 1/2)`, `ε ∈ (0, 1]`,
`δ ∈ (0, 1)` and full-support `P`, halts on every run within a universal polynomial in
`T, α⁻¹, ε⁻¹, log(1/δ)` and the input length, always outputs a dyadic balanced product `Q̂`, and
satisfies `Pr[d_TV(P, Q̂) ≤ (1 + 4/√u) OPT_α(P) + ε] ≥ 1 − δ`; for each fixed `α` its target-call
count is `O_α(S⁵ ε⁻⁶ L²)`, `S = T + 1`, `L = log(64S/(εδ))`. -/
theorem corollary_4_1 :
    ∃ (prog : Program) (c : ℕ),
      (∀ (T : ℕ), 1 ≤ T → ∀ (α ε δ : ℚ), 0 < α → α < 1 / 2 → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        ∀ (P : Cube T → ℝ), IsLaw P → FullSupport P →
          HaltsWithin prog (condOracle P) (productInput T α ε δ)
            (((T + ⌈1 / α⌉₊ + ⌈1 / ε⌉₊ + ⌈Real.log (1 / (δ : ℝ))⌉₊ +
              encLen (productInput T α ε δ) + 2 : ℕ) : ℝ) ^ c) ∧
          OutputsSatisfy prog (condOracle P) (productInput T α ε δ)
            (fun o => ∃ q : ProdCode T, o = encProd q ∧ IsProperProdCode α q) ∧
          1 - (δ : ℝ) ≤ outProb prog (condOracle P) (productInput T α ε δ)
            (fun o => ∃ q : ProdCode T, o = encProd q ∧
              tv P (prodOfCode q) ≤ (1 + 4 / Real.sqrt (uOf α)) * OPT α P + ε)) ∧
      (∀ α : ℚ, 0 < α → α < 1 / 2 → ∃ C : ℝ,
        ∀ (T : ℕ), 1 ≤ T → ∀ (ε δ : ℚ), 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        ∀ (P : Cube T → ℝ), IsLaw P → FullSupport P →
          QueriesWithin prog (condOracle P) (productInput T α ε δ)
            (C * ((T : ℝ) + 1) ^ 5 * (ε : ℝ) ^ (-6 : ℤ) *
              Real.log (64 * ((T : ℝ) + 1) / (ε * δ)) ^ 2)) := by sorry

end PrefixMixLearn.Proper
