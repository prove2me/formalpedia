-- Prove2me | Theorems.Thm_WildeQIT_Feedback_theorem_14_10_1
-- name    : WildeQIT.Feedback.theorem_14_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:03.071367+00:00
-- url     : https://prove2.me/theorems/418608af-0ecd-43f3-a92d-a248b0edf936
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
--   where $(X,Y)$ has joint law $p_X(x)\,p_{Y|X}(y|x)$. The statement has two parts:
--
--   1. $I(\mathcal N)$ is the least upper bound of the set of achievable rates, so the capacity, the supremum of that set, is $I(\mathcal N)$;
--   2. the maximum over input distributions $p_X$ is attained.
--
--   This is Shannon's channel capacity theorem: the highest rate of reliable communication over many independent uses of a classical channel is a single-letter quantity of the channel. In this mission it is the no-feedback benchmark that Theorem 21.5.1 shows feedback cannot beat.
--
--   **Formalization Note** The channel is the published `WildeQIT.Channel α β`; achievability is the published `IsAchievableChannelRate` and $I(\mathcal N)$ the published `channelMaxMutualInfo N` (supremum of `mutualInfo (N.joint p)` over input distributions `p`). Entropies are in bits. The theorem is also drafted in mission XIII; it is restated here because drafts cannot import drafts.
--
--   Differences from the source:
--   - reading: I(N) ≡ max_{pX(x)} I(X;Y) → channelMaxMutualInfo N (an sSup) together with the clause ∃ p, mutualInfo (N.joint p) = channelMaxMutualInfo N; reason: the book's max presupposes that the maximum is attained (its proof picks "a distribution that maximizes I(N)", p. 455); stating attainment is the stronger reading
--   - encoding: an (n, R − δ, ε) code, rate (log|M|)/n = R − δ → a code with M ≥ 2^{n(R−δ)} messages; reason: 2^{n(R−δ)} is rarely an integer; a code with more messages and maximal error ≤ ε yields one with any smaller number of messages by discarding messages, so "rate at least R − δ" is the book's notion
--   - encoding: input alphabet of a channel → [Nonempty α]; reason: an empty input alphabet carries no input distribution and no code, a degenerate case the book does not consider
--   - encoding: C(N) = I(N), C(N) the supremum of all achievable rates → IsLUB {R | IsAchievableChannelRate N R} (channelMaxMutualInfo N); reason: Lean's sSup of a set that is not bounded above is 0; IsLUB says I(N) is the least upper bound, which is what the equality of a real supremum with I(N) means
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 14.10.1, eq. (14.177), p. 454; code and capacity definitions, eq. (14.176), p. 454

import Definitions.Def_WildeQIT_channelCode

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.10.1, p. 454.
-/

namespace WildeQIT.Feedback

/-- **Theorem 14.10.1 (Shannon Channel Capacity)** (Wilde, arXiv:1106.1445v8, p. 454,
eq. (14.177)). The maximum mutual information `I(𝒩)` is equal to the capacity `C(𝒩)` of a
channel `𝒩 ≡ p_{Y|X}(y|x)`: `C(𝒩) = I(𝒩) ≡ max_{p_X(x)} I(X;Y)`.

The statement has two parts:
1. `I(𝒩)` is the least upper bound of the set of achievable rates, so `C(𝒩)`, the supremum of
   that set, equals `I(𝒩)`;
2. the supremum defining `I(𝒩)` is a maximum: some input distribution `p_X` attains it, as the
   book's `max_{p_X(x)}` asserts.

**Formalization Note.** The channel is the published `WildeQIT.Channel α β` (`N x` is the
distribution `p_{Y|X}(·|x)`) on finite alphabets, the input alphabet nonempty. Achievability
is the published `IsAchievableChannelRate`: for all `ε ∈ (0, 1)`, `δ > 0` and all sufficiently
large `n` a code of block length `n` with `M ≥ 2^{n(R−δ)}` messages and maximal error
probability at most `ε` (14.176). `I(𝒩)` is the published `channelMaxMutualInfo N`, a supremum
over input distributions `p` of the mutual information of the joint law `p_X(x) N(y|x)`, in
bits. Part 1 is stated with `IsLUB` rather than as `channelCapacity N = …`, because Lean's
`sSup` of a set that is not bounded above is `0`; `IsLUB` also asserts that the achievable
rates are bounded by `I(𝒩)`. The theorem is also drafted in mission XIII; it is restated here
because drafts cannot import drafts. -/
theorem theorem_14_10_1 {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    IsLUB {R : ℝ | IsAchievableChannelRate N R} (channelMaxMutualInfo N) ∧
      ∃ p : FinDist α, mutualInfo (N.joint p) = channelMaxMutualInfo N := by sorry

end WildeQIT.Feedback
