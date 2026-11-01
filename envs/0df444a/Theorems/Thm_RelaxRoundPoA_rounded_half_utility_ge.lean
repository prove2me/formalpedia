-- Prove2me | Theorems.Thm_RelaxRoundPoA_rounded_half_utility_ge
-- name    : RelaxRoundPoA.rounded_half_utility_ge
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:21.795668+00:00
-- url     : https://prove2.me/theorems/d85b5cee-0de5-44fc-97b9-1c89fb72799f
-- title:
--   §3, p.9 (third display) — $\mathbf E[u_i((b'_i,b_{-i}),v_i)]\ge\frac1{2\alpha}v_i(f'(b'_i,b_{-i}))=\frac1\alpha u'_i$
-- statement:
--   Let $M'$ and $M$ be pay-your-bid mechanisms with finite expectations on weight classes closed under halving, and let $M$ be obtained from $M'$ through an $\alpha$-approximate oblivious rounding scheme. For every bid profile $b$ drawn from the classes, every agent $i$ and every valuation $v_i\in\mathcal V_i$, put $b'=(\tfrac12v_i,b_{-i})$. Then
--
--   $$
--   \mathbf E\bigl[u_i(b',v_i)\bigr]\ \ge\ \frac1{2\alpha}\,\mathbf E\bigl[v_i(f'(b'))\bigr]\ =\ \frac1\alpha\,u_i'(b',v_i),
--   $$
--
--   where $u_i$ is the utility in $M$ and $u_i'$ the utility in $M'$. Both the inequality and the equality are asserted.
--
--   An agent bidding half its value keeps, after rounding, a $1/\alpha$ fraction of its utility in the relaxed mechanism.
--
--   Differences from the source:
--   - generalization: weight functions w: Ω → ℝ≥0 generalized to Ω′, rounding guarantee "for all w" (p.6) → each agent's bids and valuations come from an arbitrary class Val i of functions Ω′ → ℝ≥0, read on Ω by restriction; reason: over every function the rounding guarantee is unsatisfiable when Ω ≠ Ω′; every weight class of §§4–7 is an instance, and a single common class is the case of equal Val i
--   - generalization: the proofs write the outcome rule as deterministic, f(b) a point → the outcome law is any probability measure on the outcome space, almost surely an exact declared welfare maximizer where exactness is assumed; reason: p.6 allows randomized outcomes and payments; a deterministic rule is the Dirac case (verification file, check (v))
--   - encoding: expectations E[v_i(f(b))], E[p_i(b)] taken to exist → ExpFinite: every member of Val i is integrable under every outcome law on profiles; reason: excludes only the cases in which the paper's expectations are undefined; a Bochner integral of a non-integrable function would be 0
--   - reading: bids ½v_i and pretended valuations ½v_i used without comment → hypothesis HalfClosed Val: w ∈ Val i implies ½w ∈ Val i; reason: the proof bids ½v_i, so it must be an admissible bid; every class of the applications is closed under halving
--   - reading: for all w, E[w(x)] ≥ (1/α) w(x′) (p.6) → for every x′, every agent i and every w ∈ Val i: w(x′) ≤ α · E[w(x)], the expectation a lintegral; reason: p.3 says each agent is guaranteed a 1/α-fraction, and the proof of Theorem 3′ (p.9) applies the guarantee to one agent at a time; with 0 ∈ Val j for all j the total-weight form implies this one (verification file, check (iii))
--   - encoding: problem Π with outcomes Ω ⊆ Ω′; a randomized rounding scheme maps x′ to x → Ω is a set in the measurable space Ω′; the rounding is a Markov kernel R with R x′-almost every x in Ω; M's outcome law is the outcome law of M′ bound with R; reason: standard measure-theoretic form of a randomized map; measurability of the kernel is the field's standing convention
--   - generalization: the proof of Theorem 3′ has M′ solve the relaxation optimally (p.9) → exactness of M′ is not assumed; reason: this step of the proof does not use it, so the statement covers the printed case
--   - encoding: agents N = {1, …, n} → any finite type N with decidable equality; reason: relabeling; at N = ∅ every sum is 0 and the statement stays true
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, proof of Theorem 3′, p.9, third display

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_HalfClosed
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_IsPayYourBid
import Definitions.Def_RelaxRoundPoA_ExpFinite
import Definitions.Def_RelaxRoundPoA_IsObliviousRounding
import Definitions.Def_RelaxRoundPoA_IsRounded

open MeasureTheory ProbabilityTheory NNReal

namespace RelaxRoundPoA

/-- **Rounding keeps a `1/(2α)` fraction of a half-value bidder's value.**
Dütting, Kesselheim, Tardos, *Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round*,
arXiv:1511.09208v1, §3, proof of Theorem 3′, p.9, third display: "That is, for bidder `i`'s utility, we get
`E[u_i((b'_i, b_{−i}), v_i)] ≥ (1/(2α)) v_i(f'(b'_i, b_{−i})) = (1/α) u'_i((b'_i, b_{−i}), v_i)`,
where the last step uses that `M'` is a pay-your-bid mechanism as well", with `b'_i = ½ v_i`.

Let `M'` and `M` be pay-your-bid, with `M` obtained from `M'` through an α-approximate oblivious
rounding scheme `R`. For a profile `b` drawn from `Val`, an agent `i` and `v ∈ Val i`, write
`b' = (½ v, b_{−i})`. Then
1. `(1/(2α)) E[v(f'(b'))] ≤ u_i(b', v)` in `M`, and
2. `(1/(2α)) E[v(f'(b'))] = (1/α) u'_i(b', v)`, the utility in `M'`.

**Formalization Note** `f'(b')` is random in general; `E[v(f'(b'))]` is its expectation (the
paper's deterministic `v_i(f'(b'_i, b_{−i}))` is the Dirac case). -/
theorem rounded_half_utility_ge {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0))
    (Ω : Set Ω') (α : ℝ) (R : Kernel Ω' Ω') (M' M : Mechanism N Ω') (hhalf : HalfClosed Val)
    (hpay' : IsPayYourBid Val M') (hpay : IsPayYourBid Val M) (hfin' : ExpFinite Val M')
    (hfin : ExpFinite Val M) (hround : IsObliviousRounding Val Ω α R) (hrel : IsRounded Val M' R M)
    (b : N → Ω' → ℝ≥0) (hb : IsProfile Val b) (i : N) (v : Ω' → ℝ≥0) (hv : v ∈ Val i) :
    1 / (2 * α) * ∫ x, (v x : ℝ) ∂(M'.outcome (Function.update b i (fun y => v y / 2))) ≤
        utility M i (Function.update b i (fun y => v y / 2)) v ∧
      1 / (2 * α) * ∫ x, (v x : ℝ) ∂(M'.outcome (Function.update b i (fun y => v y / 2))) =
        1 / α * utility M' i (Function.update b i (fun y => v y / 2)) v := by sorry

end RelaxRoundPoA
