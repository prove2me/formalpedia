-- Prove2me | Theorems.Thm_RoundOptVSS_lemma_7_6
-- name    : RoundOptVSS.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:08:25.289569+00:00
-- url     : https://prove2.me/theorems/ef4662b5-d662-4962-ace7-41205bc0774e
-- title:
--   Lemma 7.6 — sharing-determined rejection: $\mathrm{Dec}_{O,h}(\sigma_h,k;\tau)=\bot\iff\mathrm{Reject}_O(\Gamma_O,k)=1$
-- statement:
--   **Lemma 7.6** (Sharing-determined rejection). For every honest $P_h$, every proposed assignment $k$ and every opening vector $\tau$,
--
--   $$\mathrm{Dec}_{O,h}(\sigma_h,k;\tau)=\bot\iff\mathrm{Reject}_O(\Gamma_O,k)=1.$$
--
--   In particular, whether $P_h$ outputs $\bot$ depends only on the sharing transcript and $k$, neither on the openings nor on $h$: for any two parties' private data and any two opening vectors over the same $\Gamma_O$, the two decoders return $\bot$ together. This holds in every execution, not only on the good event.
--
--   This is property (b) of Definition 6.2 in its structural form, and it reduces the compiler's key search to the public predicate $\mathrm{Reject}_O$.
--
--   Differences from the source:
--   - generalization: every honest P_h in every execution → every transcript record Γ_O, every stored-key vector, every assignment k and every opening vector τ; reason: the data of every execution are such inputs
--   - encoding: σ_h, the party's state, which contains Γ_share → σ_h = (Γ_O, stored keys); the decoder reads nothing else of the state; reason: Protocol 7 reads only these
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Lemma 7.6 (p.25), with Protocol 7 (p.23)

import Mathlib
import Definitions.Def_RoundOptVSS_WSSDecoder

namespace RoundOptVSS

/-- **Lemma 7.6** (Sharing-determined rejection), p.25 of Liu-Zhang, Masserova, *Round-Optimal
Statistical Verifiable Secret Sharing with Polynomial Complexity*, manuscript (STOC 2027
submission, sha256 3a45d95d…): for every honest `P_h`, every proposed assignment `k` and every
opening vector `τ`, `Dec_{O,h}(σ_h, k; τ) = ⊥ ⇔ Reject_O(Γ_O, k) = 1`. In particular, whether
`P_h` outputs ⊥ depends only on the sharing transcript and `k`, neither on the openings nor on
`h`. This holds in every execution.

**Formalization Note.** `σ_h = (Γ_O, key)` with `key` the party's stored keys; the statement is
for every transcript record, every stored-key vector, every `k` and every `τ` (every execution's
data is such an input). The second conjunct is the "in particular": two parties' private data
`key, key′` and two opening vectors `τ, τ′` give the same rejection decision. -/
theorem lemma_7_6 {𝔽 𝔼 : Type} [Field 𝔽] [Fintype 𝔽] [Field 𝔼] [Algebra 𝔽 𝔼]
    (W : WSSParams 𝔽) (Γ : WSSTranscript 𝔽 𝔼 W.n W.t W.h) (key : Label W.n W.t → ICKey 𝔼)
    (τ : WSSOpening 𝔼 W.n W.t W.h) (k : Assignment 𝔼 W.n) :
    (Dec W Γ key τ k = none ↔ Reject W Γ k) ∧
    ∀ (key' : Label W.n W.t → ICKey 𝔼) (τ' : WSSOpening 𝔼 W.n W.t W.h),
      (Dec W Γ key τ k = none ↔ Dec W Γ key' τ' k = none) := by sorry

end RoundOptVSS
