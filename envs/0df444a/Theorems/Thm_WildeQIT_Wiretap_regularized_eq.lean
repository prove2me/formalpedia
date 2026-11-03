-- Prove2me | Theorems.Thm_WildeQIT_Wiretap_regularized_eq
-- name    : WildeQIT.Wiretap.regularized_eq
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:15.356104+00:00
-- url     : https://prove2.me/theorems/8ea7a56d-7026-4000-9c3a-3e34712fd023
-- title:
--   Regularized mutual information equals mutual information: $I_{\mathrm{reg}}(N)=I(N)$
-- statement:
--   **Corollary 13.1.1.** Let $N$ be a classical channel with a finite, nonempty input alphabet. The regularized mutual information
--
--   $$
--   I_{\mathrm{reg}}(N)\equiv\lim_{n\to\infty}\frac1n I(N^{\otimes n})
--   $$
--
--   exists and equals the mutual information of the channel:
--
--   $$
--   I_{\mathrm{reg}}(N)=I(N).
--   $$
--
--   Here $I(N^{\otimes n})=\max_{p_{X^n}}I(X^n;Y^n)$ over all (correlated) input distributions on sequences of length $n$.
--
--   The corollary shows that the single-letter expression $I(N)$ suffices: using the channel many times with correlated inputs does not raise the mutual information per use.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). The statement is that the sequence $\tfrac1n I(N^{\otimes n})$ converges to $I(N)$; its $n=0$ term is $0/0=0$ in Lean and does not affect the limit.
--
--   Differences from the source:
--   - encoding: I_reg(N) ≡ lim_{n→∞} (1/n) I(N^{⊗n}) and I_reg(N) = I(N) → Tendsto (fun n => channelMutualInfo (powChannel N n) / n) atTop (𝓝 (channelMutualInfo N)); reason: the equation asserts that the defining limit exists and has this value; the n = 0 term 0/0 = 0 does not affect the limit
--   - encoding: I(N) ≡ max_{p_X} I(X;Y) (13.5) → channelMutualInfo N, the supremum over all input distributions; reason: the maximum is attained (continuous function on the compact simplex), so the value is the same
--   - encoding: the channel N (implicitly nonempty: a channel has inputs) → [Nonempty] instance on each input alphabet; reason: with an empty input alphabet there is no input distribution and the book's quantity is undefined (Lean's junk value 0)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 13.1.1, eq. (13.34), p. 393 (definitions (13.9)–(13.11), p. 390)

import Definitions.Def_WildeQIT_Wiretap_channelMutualInfo
import Definitions.Def_WildeQIT_Wiretap_powChannel
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Defs

namespace WildeQIT.Wiretap

open WildeQIT Filter Topology

/-- **Corollary 13.1.1 (regularized mutual information).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Corollary 13.1.1, (13.34),
p. 393, with the definitions (13.9)–(13.11), p. 390: the regularized mutual information
`I_reg(N) ≡ lim_{n→∞} (1/n) I(N^{⊗n})` of a classical channel is equal to its mutual information,
`I_reg(N) = I(N)`.

Stated as: the sequence `(1/n) I(N^{⊗n})` converges, and its limit is `I(N)`.

**Formalization Note.** `N^{⊗n}` is `powChannel N n` on sequences `Fin n → α`, with arbitrary
(correlated) input distributions on sequences, as in (13.10). The term at `n = 0` is `0/0 = 0`
and does not affect the limit. The input alphabet is nonempty. -/
theorem regularized_eq {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] [Nonempty α]
    (N : Channel α β) :
    Tendsto (fun n : ℕ => channelMutualInfo (powChannel N n) / n) atTop
      (𝓝 (channelMutualInfo N)) := by sorry

end WildeQIT.Wiretap
