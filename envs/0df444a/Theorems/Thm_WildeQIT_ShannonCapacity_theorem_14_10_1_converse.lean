-- Prove2me | Theorems.Thm_WildeQIT_ShannonCapacity_theorem_14_10_1_converse
-- name    : WildeQIT.ShannonCapacity.theorem_14_10_1_converse
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:31.137069+00:00
-- url     : https://prove2.me/theorems/0984cea9-ea38-4000-a1d7-fbc974ecc28e
-- title:
--   Theorem 14.10.1 (converse part) — every achievable rate is at most $I(\mathcal N)$
-- statement:
--   Let $\mathcal N\equiv p_{Y|X}(y|x)$ be a classical channel from a finite nonempty input alphabet $\mathcal X$ to a finite output alphabet $\mathcal Y$, with $(n,R,\varepsilon)$ channel codes, maximal error probability (14.176) and achievable rates as in §14.10. Let $I(\mathcal N)\equiv\max_{p_X}I(X;Y)$ be the maximum mutual information. Then every achievable rate $R$ for $\mathcal N$ satisfies
--
--   $$
--   R\le I(\mathcal N),
--   $$
--
--   i.e. $C(\mathcal N)\le I(\mathcal N)$, the converse half of Shannon's channel capacity theorem (14.177). It is impossible to have achievable rates exceeding the maximum mutual information. The book defers the proof to the converse of the HSW theorem in Chapter 20.
--
--   **Formalization Note** The channel is the published `WildeQIT.Channel α β`; achievability is the published `IsAchievableChannelRate`; $I(\mathcal N)$ is the published `channelMaxMutualInfo N`. Entropies are in bits.
--
--   Differences from the source:
--   - encoding: an (n, R − δ, ε) code, rate (log|M|)/n = R − δ → a code with M ≥ 2^{n(R−δ)} messages; reason: 2^{n(R−δ)} is rarely an integer; a code with more messages and maximal error ≤ ε yields one with any smaller number of messages by discarding messages, so "rate at least R − δ" is the book's notion
--   - encoding: I(N) ≡ max_{pX} I(X;Y) → sSup over input distributions (channelMaxMutualInfo); reason: the maximum exists (the goal item states attainment), so the supremum is the maximum
--   - encoding: input alphabet of a channel → [Nonempty α]; reason: an empty input alphabet carries no input distribution and no code, a degenerate case the book does not consider
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 14.10.1, eq. (14.177), pp. 454–455 (converse deferred to Chapter 20)

import Definitions.Def_WildeQIT_channelCode

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 14.10.1, converse
part, pp. 454–455.
-/

namespace WildeQIT.ShannonCapacity

/-- **Theorem 14.10.1, converse part** (Wilde, arXiv:1106.1445v8, pp. 454–455; the book defers
its proof to the HSW converse of Chapter 20). No rate exceeding the maximum mutual information
`I(𝒩) = max_{p_X} I(X;Y)` is achievable for the classical channel `𝒩 ≡ p_{Y|X}`: every
achievable rate `R` satisfies `R ≤ I(𝒩)`. This is the direction `C(𝒩) ≤ I(𝒩)` of (14.177).

Formalization Note: the channel is the published `WildeQIT.Channel α β` on finite, nonempty
alphabets; achievability is the published `IsAchievableChannelRate` (maximal error
probability, (14.176), with `M ≥ 2^{n(R−δ)}` messages); `I(𝒩)` is the published
`channelMaxMutualInfo N`, in bits. -/
theorem theorem_14_10_1_converse {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (N : Channel α β) (R : ℝ) (hR : IsAchievableChannelRate N R) :
    R ≤ channelMaxMutualInfo N := by sorry

end WildeQIT.ShannonCapacity
