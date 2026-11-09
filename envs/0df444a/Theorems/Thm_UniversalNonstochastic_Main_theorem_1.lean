-- Prove2me | Theorems.Thm_UniversalNonstochastic_Main_theorem_1
-- name    : UniversalNonstochastic.Main.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:43.803198+00:00
-- url     : https://prove2.me/theorems/12fe61ac-aeb8-4a1b-9a04-077cb75ceb6c
-- title:
--   Theorem 1 — nonstochastic objects have universal mass $\Theta(\tau(\alpha))$
-- statement:
--   Let $\mathbf m$ be a universal semimeasure on $\mathbb N=\{1,2,\dots\}$ with tail $\tau(t)=\mathbf m(\{n:n>t\})$. Let $K$ be prefix complexity, and let $N_{\alpha,\beta}$ be the set of $(\alpha,\beta)$-nonstochastic objects: those $\omega$ for which no finite set $\Omega\ni\omega$ has $K(\Omega)\le\alpha$ and $K(\omega\mid\Omega)\ge\log_2|\Omega|-\beta$. There exists $c>1$ such that, for all $\alpha\in\mathbb N_0$ and all real $\beta$ with $0\le\beta\le2^{2^\alpha}$,
--   $$\tau(\alpha)/c\;\le\;\mathbf m(N_{\alpha,\beta})\;\le\;c\,\tau(\alpha). \tag{1}$$
--
--   The constant $c$ is uniform in $\alpha$ and $\beta$. Since $\tau$ decreases to $0$ more slowly than any computable positive nonincreasing function tending to $0$, the theorem says that the universal machine produces nonstochastic objects with a probability that decays extremely slowly. This is the first key result of the paper.
--
--   **Formalization Note** The universal semimeasure and the optimal prefix decoder are arbitrary, and are chosen before the constant $c$. $\beta$ ranges over the full real interval $[0,2^{2^\alpha}]$.
--
--   Differences from the source:
--   - encoding: objects ω in a basic space 𝓧 in computable bijection with ℕ → objects are positive integers ℕ+ (the paper’s ℕ = {1,2,…}), coded by themselves; reason: the source explicitly permits replacing 𝓧 by ℕ in every formal statement (p.4); ObjectEncoding and the transport functions implement its fixed computable bijection without changing any instance
--   - encoding: K: prefix complexity defined by a fixed optimal decoder → U: an arbitrary optimal conditional prefix decoder; complexity is minimal halting-program length in ℕ∞, unconditional complexity uses condition 0; reason: the source fixes any optimal decoders; ℕ∞ is the exact infimum (⊤ only on no description, which optimality excludes); every statement is quantified over all such choices before its constants
--   - encoding: m: a fixed universal semimeasure on ℕ, m(A) = Σ_{a∈A} m(a) → m : UniversalSemimeasure (arbitrary), mass m A = real tsum of the indicator; reason: the weights are nonnegative with partial sums ≤ 1, so the real sum is the true sum; the statement is quantified over every universal semimeasure
--   - encoding: β ∈ [0, ∞] with β ≤ 2^{2^α} → β : ℝ with 0 ≤ β and β ≤ 2^(2^α); reason: the upper bound excludes β = ∞; the standing domain β ≥ 0 is written as a hypothesis
--   - encoding: K(ω | Ω) ≥ log₂|Ω| − β in the finite-set stochasticity predicate → the comparison is in EReal, with finite real β coerced to EReal; reason: membership gives positive cardinality and optimality gives finite complexity; EReal subtraction therefore equals the source’s real subtraction for every parameter in the theorem
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Theorem 1, eq. (1), p.5 (PDF p.5); proof Sect. A.2 p.17

import Mathlib
import Definitions.Def_UniversalNonstochastic_Main_UniversalMeasure
import Definitions.Def_UniversalNonstochastic_Main_Complexity
import Definitions.Def_UniversalNonstochastic_Main_Stochasticity

namespace UniversalNonstochastic.Main

/-- Theorem 1, p.5, equation (1): there is `c > 1` such that for all `α ∈ ℕ₀` and all real
`0 ≤ β ≤ 2^{2^α}`, `τ(α)/c ≤ m(N_{α,β}) ≤ c τ(α)`. -/
theorem theorem_1 (m : UniversalSemimeasure) (U : OptimalPrefixDecoder) :
    ∃ c : ℝ, 1 < c ∧ ∀ (α : ℕ) (β : ℝ), 0 ≤ β → β ≤ (2 : ℝ) ^ (2 ^ α) →
      tail m (α : ℝ) / c ≤ mass m (nonstochastic U α β) ∧
        mass m (nonstochastic U α β) ≤ c * tail m (α : ℝ) := by sorry

end UniversalNonstochastic.Main
