-- Prove2me | Theorems.Thm_RelaxRoundPoA_isSmooth_of_half
-- name    : RelaxRoundPoA.isSmooth_of_half
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:51:40.615995+00:00
-- url     : https://prove2.me/theorems/038747f8-624f-4547-873a-0a3432033b90
-- title:
--   §2, p.7 — smoothness for half-value deviations is smoothness
-- statement:
--   Let the weight classes be closed under halving. If a mechanism $M$ with feasible outcomes $F$ is $(\lambda,\mu)$-smooth for deviations to half the value, then it is $(\lambda,\mu)$-smooth. The deviation $b_i'=\tfrac12v_i$ witnesses smoothness; it is deterministic and depends only on agent $i$'s own valuation $v_i$, not on its bid or on the other agents' valuations (semi-smoothness).
--
--   This is the last step of the proof of Theorem 3, and it turns the half-value conclusion of Theorem 3′ into the printed "$(\lambda/\alpha,\mu)$-smooth".
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - reading: bids ½v_i and pretended valuations ½v_i used without comment → hypothesis HalfClosed Val: w ∈ Val i implies ½w ∈ Val i; reason: the proof bids ½v_i, so it must be an admissible bid; every class of the applications is closed under halving
--   - encoding: λ · max_{x∈Ω} Σ_i v_i(x), i.e. λ OPT(v) → the inequality holds for every feasible outcome x; reason: equivalent when the maximum exists; avoids a real supremum, which is 0 on an unbounded set
--   - encoding: a possibly randomized deviation strategy b′_i (p.7) → a random variable into Val i on an arbitrary probability space (RandomBid), whose expected utility is integrable; reason: Mathlib has no σ-algebra on a class of functions; every mixture of bids arises this way
--   - reading: remark that the deviation b′_i of the paper's smoothness proofs depends only on v_i (semi-smoothness) → smoothness for deviations to half the value implies (λ, µ)-smoothness, witnessed by the deterministic deviation ½v_i; reason: the remark is what makes a half-value smoothness proof a smoothness proof; stated as the implication Theorem 3 needs
--   - generalization: a pay-your-bid mechanism with payments p(b) ∈ ℝ≥0 (p.6) → any mechanism, pay-your-bid not assumed, with arbitrary real expected payments; reason: the implication does not depend on the payments; nonnegative payments are a case of it
--   - generalization: the mechanism's outcome space Ω (p.8) → an arbitrary set Feas ⊆ Ω′ of feasible outcomes; reason: Feas = Set.univ is the relaxation M′ of Theorem 3, and the outcome space of any mechanism is a case of it
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.7

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_IsSmooth
import Definitions.Def_RelaxRoundPoA_IsSmoothHalf

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Smoothness for half-value deviations is smoothness.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §2, p.7: "In fact, our smoothness proofs show an even slightly stronger property,
semi-smoothness as defined by [8]: the deviation strategy `b'_i` only depends on the respective
agent's valuation `v_i`, but not on the agent's bid `b_i` or the other agents' valuations `v_{−i}`."

If `M` is (λ, µ)-smooth for deviations to half the value over `Feas`, then `M` is (λ, µ)-smooth over
`Feas`, witnessed by the deterministic deviation `b'_i = ½ v_i`, which depends on `v_i` only.

**Formalization Note** `HalfClosed Val` makes `½ v_i` an admissible bid; the deterministic deviation
is a `RandomBid` on a one-point probability space. -/
theorem isSmooth_of_half {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (lam mu : ℝ) (hhalf : HalfClosed Val)
    (h : IsSmoothHalf Val Feas M lam mu) :
    IsSmooth Val Feas M lam mu := by sorry

end RelaxRoundPoA
