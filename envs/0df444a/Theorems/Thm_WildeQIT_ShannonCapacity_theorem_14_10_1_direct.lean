-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_theorem_14_10_1_direct
-- name    : WildeQIT.ShannonCapacity.theorem_14_10_1_direct
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T18:36:26.297853+00:00
-- url     : https://prove2.me/theorems/07559635-2d7b-45ad-ae39-e1f94a3f1af9
-- title:
--   Theorem 14.10.1 (direct coding theorem) — the maximum mutual information $I(\mathcal N)$ is an achievable rate
-- statement:
--   Let $\mathcal N\equiv p_{Y|X}(y|x)$ be a classical channel from a finite nonempty input alphabet $\mathcal X$ to a finite output alphabet $\mathcal Y$, used $n$ times independently, $p_{Y^n|X^n}(y^n|x^n)=\prod_i p_{Y|X}(y_i|x_i)$. An $(n,R,\varepsilon)$ channel code consists of an encoding $E_n:\mathcal M\to\mathcal X^n$ and a decoding $D_n:\mathcal Y^n\to\mathcal M$ with rate $\frac1n\log|\mathcal M|=R$ and maximal error probability
--
--   $$
--   p_e\equiv\max_m\Pr\{D_n(\mathcal N^n(E_n(m)))\neq m\}\le\varepsilon . \tag{14.176}
--   $$
--
--   A rate $R$ is achievable if for all $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is an $(n,R-\delta,\varepsilon)$ channel code. Let $I(\mathcal N)\equiv\max_{p_X}I(X;Y)$ be the maximum mutual information, where $(X,Y)$ has joint law $p_X(x)\,p_{Y|X}(y|x)$. Then
--
--   $$
--   I(\mathcal N)\ \text{is an achievable rate for } \mathcal N ,
--   $$
--
--   i.e. $I(\mathcal N)\le C(\mathcal N)$, the direct half of Shannon's channel capacity theorem (14.177).
--
--   **Formalization Note** The channel is the published `WildeQIT.Channel α β`; codes, error probabilities and achievability are the published `WildeQIT.ChannelCode`, `ChannelCode.errorProb` and `IsAchievableChannelRate`; $I(\mathcal N)$ is the published `channelMaxMutualInfo N`. Entropies are in bits.
--
--   Differences from the source:
--   - encoding: an (n, R − δ, ε) code, rate (log|M|)/n = R − δ → a code with M ≥ 2^{n(R−δ)} messages; reason: 2^{n(R−δ)} is rarely an integer; a code with more messages and maximal error ≤ ε yields one with any smaller number of messages by discarding messages, so "rate at least R − δ" is the book's notion
--   - encoding: I(N) ≡ max_{pX} I(X;Y) → sSup over input distributions (channelMaxMutualInfo); reason: the maximum exists (the goal item states attainment), so the supremum is the maximum
--   - encoding: input alphabet of a channel → [Nonempty α]; reason: an empty input alphabet carries no input distribution and no code, a degenerate case the book does not consider
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 14.10.1, eq. (14.177), p. 454; code definition eq. (14.176), p. 454; proof of the direct part, pp. 454–458

import Definitions.Def_WildeQIT_channelCode

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.10.1, direct
coding theorem, pp. 454–458.
-/

namespace WildeQIT.ShannonCapacity

/-- **Theorem 14.10.1, direct coding theorem** (Wilde, arXiv:1106.1445v8, pp. 454–458).
The maximum mutual information `I(𝒩) = max_{p_X} I(X;Y)` is an achievable rate for the classical
channel `𝒩 ≡ p_{Y|X}`: for every `ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` there is an
`(n, I(𝒩) − δ, ε)` channel code. This is the direction `I(𝒩) ≤ C(𝒩)` of (14.177).

Formalization Note: the channel is the published `WildeQIT.Channel α β` (a distribution
`N x` on the finite output alphabet `β` for each letter `x` of the finite, nonempty input
alphabet `α`). Achievability is the published `IsAchievableChannelRate`: for all
`ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` a code of block length `n` with
`M ≥ 2^{n(R−δ)}` messages, a deterministic encoder and decoder, and maximal error probability
`max_m Pr{Dₙ(𝒩ⁿ(Eₙ(m))) ≠ m} ≤ ε` (14.176). `I(𝒩)` is the published `channelMaxMutualInfo N`,
the supremum over input distributions `p` of `I(X;Y)` for the joint law `p_X(x) N(y|x)`;
entropies are in bits. -/
theorem theorem_14_10_1_direct {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) :
    IsAchievableChannelRate N (channelMaxMutualInfo N) := by sorry

end WildeQIT.ShannonCapacity
