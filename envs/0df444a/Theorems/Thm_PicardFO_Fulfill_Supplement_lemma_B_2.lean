-- Prove2me | Theorems.Thm_PicardFO_Fulfill_Supplement_lemma_B_2
-- name    : PicardFO.Fulfill.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:09:38.421549+00:00
-- url     : https://prove2.me/theorems/cae3f458-30c0-4dfb-b0d0-5c1f1a5ab32e
-- title:
--   Lemma B.2 — exact numerical warehouse correction on the next replenishment interval
-- statement:
--   Consider any real-valued OWMR model and arbitrary local policies satisfying Appendix B.2, with valid upper-bounded initial stocks and any retailer ownership map. Let $t_1\in\{1,\ldots,T\}$ be a strictly positive sequential warehouse replenishment and $t_2$ its next such time, with terminal fallback $T$. Start a sweep (iteration $k$) from an arbitrary previous cache $\beta$. Assume that every process has the correct active-retailer request at every order, and the correct numerical warehouse replenishment through order $t_1$. If $\alpha$ is the owner-assembled cache of this sweep, then two additional sweeps give
--   $$
--   q^{k+2}_{t,0}=q^{\rm seq}_{t,0}\qquad(t_1<t\le t_2).
--   $$
--   The intermediate cached central quantities have no correctness premise. All processes are quantified, the endpoint is included even when terminal time has no replenishment, and the conclusion concerns exact real quantities. This is the interval result used in the source proof of companion Theorem B.1; it supplies no claim about the boundary before the first replenishment.
--
--   **Formalization Note** The statement calls the three owner-assembled caches $\alpha,\alpha',\alpha''$. It instantiates the published numerical Algorithm 1 with its feasibility fallback, rather than the reset-to-$S$ recurrence in the proof sketch. The full local nonnegativity and requested-capacity conditions, upper storage constraints and conventional order-up-to parameter bounds are bundled in the Model and Policy definitions.
--
--   Differences from the source:
--   - reading: the proof sketch resets warehouse stock to S on positive cached central decisions → numerical Algorithm 1 replays the full cached replenishment pair, with its feasibility fallback; reason: eq. (12), the real-valued action definition and Algorithm 1 specify quantities; reset-to-S replay is not equivalent, and the interval argument is checked for numerical replay directly
--   - generalization: iteration k of the initialized Picard run → a sweep from any real-valued previous cache beta, followed by two further sweeps; reason: substitute the actual cache at k-1 to obtain precisely iterations k, k+1 and k+2; the same all-process hypotheses are retained
--   - generalization: finitely many processes owning a partition of retailers → an arbitrary process type and any retailer ownership map; reason: each finite partition is obtained by taking the process type Fin M and its owner map; the argument only uses the unique owner of each retailer
--   - reading: t2 = min{t > t1 : q_seq(t,0)>0} union {T} → the minimum of the future replenishment times union the singleton {T}; reason: the printed expression is ill-typed; the prose specifies the next replenishment with terminal fallback
--   - encoding: 1-based orders and the displayed R count starting at zero → 0-based computational orders, with sourceAction supplying an unexecuted zero-action sentinel at source time zero; reason: preserves every actual order and the displayed inclusive sum without counting a fictitious initial replenishment
--   - reading: demand, storage capacities and an (s,S) order-up-to policy → nonnegative demand and capacities, and 0 <= s <= S <= c0; retailer capacities at most s; reason: makes the operational conventions explicit; no initial-stock lower bound or local-policy regularity is added
-- source:
--   Farias et al., Speeding up Policy Simulation in Supply Chain RL, arXiv:2406.01939v2, p. 15, Lemma B.2

import Mathlib
import Definitions.Def_PicardFO_Fulfill_Supplement_Picard

namespace PicardFO.Fulfill.Supplement

/-- B.2 for numerical actions, with arbitrary previous cache β. The first sweep
is iteration k, α its cache; the next two sweeps are k+1 and k+2. -/
theorem lemma_B_2 {N : ℕ} {Ω ι : Type*}
    (D : Model N Ω) (P : Policy N Ω) (x : Stock N) (ω : ℕ → Ω)
    (own : Fin N → ι) (T t₁ : ℕ) (β : ℕ → Action)
    (hP : P.Admissible D) (hx : D.Valid x)
    (ht₁ : 1 ≤ t₁) (ht₁T : t₁ ≤ T)
    (hpositive : 0 < (Model.sourceAction (D.sequential P x ω) t₁).1)
    (hlocal : ∀ (m : ι) (t : ℕ), t < T →
      (D.process P x ω own β m t).2 = (D.sequential P x ω t).2)
    (hprefix : ∀ (m : ι) (t : ℕ), t < t₁ →
      (D.process P x ω own β m t).1 = (D.sequential P x ω t).1) :
    let α := D.sweep P x ω own β
    let α' := D.sweep P x ω own α
    let α'' := D.sweep P x ω own α'
    ∀ t : ℕ, t₁ < t → t ≤ D.nextReplenishment P x ω T t₁ →
      (Model.sourceAction α'' t).1 = (Model.sourceAction (D.sequential P x ω) t).1 := by sorry

end PicardFO.Fulfill.Supplement
