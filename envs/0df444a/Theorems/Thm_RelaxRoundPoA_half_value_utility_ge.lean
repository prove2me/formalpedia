-- Prove2me | Theorems.Thm_RelaxRoundPoA_half_value_utility_ge
-- name    : RelaxRoundPoA.half_value_utility_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:50:50.740833+00:00
-- url     : https://prove2.me/theorems/8626b747-780b-4c89-92b8-0e13b5e383d5
-- title:
--   §3, p.8 (last display) — $u_i((\tfrac12v_i,b_{-i}),v_i)\ge u_i((b''_i,b_{-i}),\tfrac12v_i)$
-- statement:
--   Let $M=(f,p)$ be a pay-your-bid exact declared welfare maximizer over $F$ with finite expectations on weight classes closed under halving. For every bid profile $b$ drawn from the classes, every agent $i$, every valuation $v_i\in\mathcal V_i$ and every bid $b_i''\in\mathcal V_i$,
--
--   $$
--   u_i\bigl((\tfrac12v_i,b_{-i}),v_i\bigr)\ \ge\ u_i\bigl((b_i'',b_{-i}),\tfrac12v_i\bigr).
--   $$
--
--   Bidding half one's value with true value $v_i$ is at least as good as any bid $b_i''$ made by an agent whose value is $\tfrac12v_i$. Summed over agents and combined with smoothness at the valuation profile $\tfrac12v$, this proves Lemma 1.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - reading: bids ½v_i and pretended valuations ½v_i used without comment → hypothesis HalfClosed Val: w ∈ Val i implies ½w ∈ Val i; reason: the proof bids ½v_i, so it must be an admissible bid; every class of the applications is closed under halving
--   - generalization: the mechanism's outcome space Ω (p.8) → an arbitrary set Feas ⊆ Ω′ of feasible outcomes; reason: Feas = Set.univ is the relaxation M′ of Theorem 3, and the outcome space of any mechanism is a case of it
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, proof of Lemma 1, p.8, last display

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsExactMaximizer

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **Bidding half the value beats any bid made with half the value.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §3, proof of Lemma 1, p.8, last display: "By furthermore changing `b'_i` back to `½ v_i`, we
get `u_i((b'_i, b_{−i}), v_i) ≥ ½ v_i(f(b''_i, b_{−i})) − p_i(b''_i, b_{−i}) = u_i((b''_i, b_{−i}), ½ v_i)`",
where `b'_i = ½ v_i`.

For a pay-your-bid exact declared welfare maximizer `M` over `Feas`, a profile `b` drawn from `Val`,
an agent `i`, a valuation `v ∈ Val i` and any bid `b'' ∈ Val i`:
`u_i((b'', b_{−i}), ½ v) ≤ u_i((½ v, b_{−i}), v)`.

**Formalization Note** `HalfClosed Val` makes `½ v` an admissible bid. The outcome rule is
randomized (a deterministic rule is the Dirac case); `ExpFinite` makes the expectations finite. -/
theorem half_value_utility_ge {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Feas : Set Ω') (M : Mechanism N Ω') (hhalf : HalfClosed Val) (hpay : IsPayYourBid Val M)
    (hfin : ExpFinite Val M) (hexact : IsExactMaximizer Val Feas M)
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) (v b'' : Ω' → ℝ≥0) (hv : v ∈ Val i)
    (hb'' : b'' ∈ Val i) :
    utility M i (Function.update b i b'') (fun x => v x / 2) ≤
      utility M i (Function.update b i (fun x => v x / 2)) v := by sorry

end RelaxRoundPoA
