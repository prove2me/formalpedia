-- Prove2me | Theorems.Thm_WildeQIT_Wiretap_channelMutualInfo_additive
-- name    : WildeQIT.Wiretap.channelMutualInfo_additive
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:04.394969+00:00
-- url     : https://prove2.me/theorems/45c3085e-04af-4300-b20a-a97d4636fe75
-- title:
--   Additivity of the mutual information of classical channels: $I(N_1\otimes N_2)=I(N_1)+I(N_2)$
-- statement:
--   **Theorem 13.1.1 (Additivity of Mutual Information of Classical Channels).** Let $N_1\equiv p_{Y_1|X_1}$ and $N_2\equiv p_{Y_2|X_2}$ be classical channels with finite, nonempty input alphabets, and let $N_1\otimes N_2$ be their joint channel. Then
--
--   $$
--   I(N_1\otimes N_2)=I(N_1)+I(N_2),
--   $$
--
--   where $I(N)=\max_{p_X}I(X;Y)$, and for the joint channel the maximum ranges over all, possibly correlated, input distributions $p_{X_1,X_2}$.
--
--   The theorem says that correlations between the inputs of independent classical channels cannot increase their mutual information; it is the basis of the single-letter capacity formula of classical information theory.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
--
--   Differences from the source:
--   - encoding: I(N) ≡ max_{p_X} I(X;Y) (13.5) → channelMutualInfo N, the supremum over all input distributions; reason: the maximum is attained (continuous function on the compact simplex), so the value is the same
--   - encoding: the channels N1, N2 (implicitly nonempty: a channel has inputs) → [Nonempty] instance on each input alphabet; reason: with an empty input alphabet there is no input distribution and the book's quantity is undefined (Lean's junk value 0)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 13.1.1, eq. (13.17), p. 391 (definitions (13.15)–(13.16))

import Definitions.Def_WildeQIT_Wiretap_channelMutualInfo
import Definitions.Def_WildeQIT_Wiretap_prodChannel

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Theorem 13.1.1 (Additivity of Mutual Information of Classical Channels).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 13.1.1, (13.17),
p. 391: the mutual information of the classical joint channel `N₁ ⊗ N₂` is the sum of their
individual mutual informations, `I(N₁ ⊗ N₂) = I(N₁) + I(N₂)`.

The joint channel's input distributions range over all distributions on pairs `(x₁, x₂)`
(correlated inputs, (13.16)).

**Formalization Note.** Finite alphabets; `I(N)` is the supremum of `channelMutualInfo`. The input
alphabets are nonempty (otherwise no input distribution exists and the book's quantity is
undefined). -/
theorem channelMutualInfo_additive {α₁ α₂ β₁ β₂ : Type} [Fintype α₁] [Fintype α₂]
    [Fintype β₁] [Fintype β₂] [Nonempty α₁] [Nonempty α₂]
    (N₁ : Channel α₁ β₁) (N₂ : Channel α₂ β₂) :
    channelMutualInfo (prodChannel N₁ N₂) = channelMutualInfo N₁ + channelMutualInfo N₂ := by sorry

end WildeQIT.Wiretap
