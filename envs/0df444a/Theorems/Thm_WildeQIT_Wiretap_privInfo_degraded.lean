-- Prove2me | Theorems.Thm_WildeQIT_Wiretap_privInfo_degraded
-- name    : WildeQIT.Wiretap.privInfo_degraded
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:28:55.598321+00:00
-- url     : https://prove2.me/theorems/e59f0ef6-64e6-46bc-8bda-7df824d9ccbd
-- title:
--   Private information of a degraded wiretap channel: $P(N)=\max_{p_X}[I(X;Y)-I(X;Z)]$
-- statement:
--   **Proposition 13.2.1.** Let $N\equiv p_{Y,Z|X}$ be a physically degraded classical wiretap channel with a finite, nonempty input alphabet. Then its private information simplifies to
--
--   $$
--   P(N)=\max_{p_X(x)}\bigl[I(X;Y)-I(X;Z)\bigr],
--   $$
--
--   where $(X,Y,Z)$ has the joint distribution $p_X(x)\,p_{Y,Z|X}(y,z|x)$. That is: $P(N)$ equals the supremum of $I(X;Y)-I(X;Z)$ over input distributions $p_X$, and some input distribution attains it.
--
--   For degraded channels no auxiliary random variable is needed: Alice can send her variable directly into the channel.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second).
--
--   Differences from the source:
--   - encoding: P(N) ≡ max_{p_{U,X}} [I(U;Y) − I(U;Z)] over auxiliary U of any alphabet (13.57) → privInfo N, the supremum over U with alphabet Fin n for every n ∈ ℕ; reason: every finite alphabet is in bijection with some Fin n and mutual information is invariant under relabeling; the book does not prove attainment, so its max is read as the supremum of the same set
--   - encoding: P(N) = max_{p_X} [I(X;Y) − I(X;Z)] → privInfo N = ⨆ p, [I(X;Y) − I(X;Z)] ∧ ∃ p, privInfo N = I(X;Y) − I(X;Z); reason: a maximum is a supremum that is attained; both parts are stated
--   - encoding: X → Y → Z Markov chain, p_{Y,Z|X} = p_{Z|Y} p_{Y|X} → IsDegraded N: ∃ channel D, N(y,z|x) = N_Y(y|x) D(z|y); reason: the book's factorization, with p_{Y|X} the Y-marginal of the channel
--   - encoding: the channel N (implicitly nonempty: a channel has inputs) → [Nonempty] instance on each input alphabet; reason: with an empty input alphabet there is no input distribution and the book's quantity is undefined (Lean's junk value 0)
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Proposition 13.2.1, eq. (13.73), p. 399 (definition of physical degradedness, p. 399)

import Definitions.Def_WildeQIT_Wiretap_privInfo
import Definitions.Def_WiretapFeedback_jointLaw
import Definitions.Def_WildeQIT_Wiretap_IsDegraded

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Proposition 13.2.1 (private information of a degraded wiretap channel).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Proposition 13.2.1, (13.73),
p. 399: the private information of a degraded classical wiretap channel `N ≡ p_{Y,Z|X}` simplifies
to `P(N) = max_{p_X(x)} [I(X; Y) − I(X; Z)]`.

Two clauses: `P(N)` equals the supremum over input distributions `p_X` of `I(X; Y) − I(X; Z)`,
and this supremum is a maximum (some `p_X` attains `P(N)`). Here `(X, Y, Z)` has the joint
distribution `p_X(x) p_{Y,Z|X}(y, z|x)` (`WiretapFeedback.jointLaw p N` on `α × β × γ`), whose `margXY` and
`margXZ` are `(X, Y)` and `(X, Z)`.

**Formalization Note.** Degradedness is `IsDegraded N` (physical degradedness, p. 399). The
input alphabet is nonempty. -/
theorem privInfo_degraded {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [Nonempty α]
    (N : WiretapChannel α β γ) (hN : IsDegraded N) :
    privInfo N =
        (⨆ p : FinDist α, (mutualInfo (WiretapFeedback.jointLaw p N).margXY - mutualInfo (WiretapFeedback.jointLaw p N).margXZ)) ∧
      ∃ p : FinDist α,
        privInfo N = mutualInfo (WiretapFeedback.jointLaw p N).margXY - mutualInfo (WiretapFeedback.jointLaw p N).margXZ := by sorry

end WildeQIT.Wiretap
