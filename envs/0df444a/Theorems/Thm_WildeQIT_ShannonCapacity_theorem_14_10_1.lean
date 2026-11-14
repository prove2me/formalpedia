-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_theorem_14_10_1
-- name    : WildeQIT.ShannonCapacity.theorem_14_10_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:36:24.613683+00:00
-- url     : https://prove2.me/theorems/9e3c6433-2009-463e-addd-419f075b8b7b
-- title:
--   Theorem 14.10.1 (Shannon Channel Capacity): $C(\mathcal N)=I(\mathcal N)\equiv\max_{p_X}I(X;Y)$
-- statement:
--   Let $\mathcal N\equiv p_{Y|X}(y|x)$ be a classical channel from a finite nonempty input alphabet $\mathcal X$ to a finite output alphabet $\mathcal Y$, used $n$ times independently. An $(n,R,\varepsilon)$ channel code has an encoding $E_n:\mathcal M\to\mathcal X^n$, a decoding $D_n:\mathcal Y^n\to\mathcal M$, rate $\frac1n\log|\mathcal M|=R$ and maximal error probability $\max_m\Pr\{D_n(\mathcal N^n(E_n(m)))\neq m\}\le\varepsilon$ (14.176). A rate $R$ is achievable if for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is an $(n,R-\delta,\varepsilon)$ code, and the capacity $C(\mathcal N)$ is the supremum of all achievable rates.
--
--   The maximum mutual information equals the capacity:
--
--   $$
--   C(\mathcal N)=I(\mathcal N)\equiv\max_{p_X(x)}I(X;Y), \tag{14.177}
--   $$
--
--   where $(X,Y)$ has joint law $p_X(x)\,p_{Y|X}(y|x)$ and the maximum over input distributions $p_X$ is attained.
--
--   This is Shannon's channel capacity theorem: the highest rate of reliable communication over many independent uses of a classical channel is a single-letter quantity of the channel.
--
--   **Formalization Note** The channel is the published `WildeQIT.Channel α β`; $C(\mathcal N)$ is the published `channelCapacity N` (supremum of the rates satisfying `IsAchievableChannelRate`) and $I(\mathcal N)$ the published `channelMaxMutualInfo N` (supremum of `mutualInfo (N.joint p)` over input distributions `p`). The theorem states the equality and that some input distribution attains the supremum. Entropies are in bits.
--
--   Differences from the source:
--   - reading: I(N) ≡ max_{pX(x)} I(X;Y) → channelMaxMutualInfo N (an sSup) together with the clause ∃ p, mutualInfo (N.joint p) = channelMaxMutualInfo N; reason: the book's max presupposes that the maximum is attained (its proof picks "a distribution that maximizes I(N)", p. 455); stating attainment is the stronger reading
--   - encoding: an (n, R − δ, ε) code, rate (log|M|)/n = R − δ → a code with M ≥ 2^{n(R−δ)} messages; reason: 2^{n(R−δ)} is rarely an integer; a code with more messages and maximal error ≤ ε yields one with any smaller number of messages by discarding messages, so "rate at least R − δ" is the book's notion
--   - encoding: input alphabet of a channel → [Nonempty α]; reason: an empty input alphabet carries no input distribution and no code, a degenerate case the book does not consider
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 14.10.1, eq. (14.177), p. 454; code and capacity definitions, eq. (14.176), p. 454

import Definitions.Def_WildeQIT_channelCode

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.10.1, p. 454.
-/

namespace WildeQIT.ShannonCapacity

/-- **Theorem 14.10.1 (Shannon Channel Capacity)** (Wilde, arXiv:1106.1445v8, p. 454,
eq. (14.177)). The maximum mutual information `I(𝒩)` is equal to the capacity `C(𝒩)` of a
channel `𝒩 ≡ p_{Y|X}(y|x)`: `C(𝒩) = I(𝒩) ≡ max_{p_X(x)} I(X;Y)`.

The statement has two parts:
1. `C(𝒩) = I(𝒩)`, where `C(𝒩)` is the supremum of the achievable rates and `I(𝒩)` the
   supremum over input distributions of the mutual information;
2. the supremum defining `I(𝒩)` is a maximum: some input distribution `p_X` attains it, as the
   book's `max_{p_X(x)}` asserts.

Formalization Note: the channel is the published `WildeQIT.Channel α β` (`N x` is the
distribution `p_{Y|X}(·|x)`) on finite alphabets, the input alphabet nonempty. `C(𝒩)` is the
published `channelCapacity N`: the supremum of the rates `R` that are achievable in the sense of
§14.10 — for all `ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` a code of block length
`n` with `M ≥ 2^{n(R−δ)}` messages and maximal error probability at most `ε` (14.176). `I(𝒩)`
is the published `channelMaxMutualInfo N`, a supremum over input distributions `p` of the
mutual information `I(X;Y)` of the joint law `p_X(x) N(y|x)`; part 2 makes it the book's
maximum. Entropies are in bits. -/
theorem theorem_14_10_1 {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    channelCapacity N = channelMaxMutualInfo N ∧
      ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by sorry

end WildeQIT.ShannonCapacity
