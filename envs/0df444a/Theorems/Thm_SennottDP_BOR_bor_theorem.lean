-- Prove2me | Theorems.Thm_SennottDP_BOR_bor_theorem
-- name    : SennottDP.BOR.bor_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:30:31.467914+00:00
-- url     : https://prove2.me/theorems/e6b206ef-9290-4534-a7f4-a8a1472d568c
-- title:
--   Theorem 7.5.6 — under (BOR): (SEN), the ACOE, and positive recurrence of optimal stationary policies
-- statement:
--   Assume the (BOR) assumptions hold for the distinguished state $z$, the $z$ standard policy $d$ and $\varepsilon>0$: (BOR1) $d$ is $z$ standard with positive recurrent class $R_d$; (BOR2) $D=\{i\mid C(i,a)\le J_d+\varepsilon\text{ for some }a\}$ is finite; (BOR3) for every $i\in D-R_d$ there is a policy $\theta_i\in\Re^*(z,i)$. Let $J$ be the minimum average cost; it is a finite constant with $J=\lim_{\alpha\to1^-}(1-\alpha)V_\alpha(i)$ for all $i$. Then:
--
--   1. The (SEN) assumptions hold, a limit function exists, and the ACOE is valid: every limit function $h$ satisfies
--   $$
--   J+h(i)=\min_{a\in A_i}\Big\{C(i,a)+\sum_jP_{ij}(a)h(j)\Big\},\qquad i\in S.
--   $$
--   2. The Markov chain induced by any average cost optimal stationary policy $e$ has at least one positive recurrent state in $D(e)=\{i\mid C(i,e)\le J+\varepsilon\}$. With $R(e)$ the set of positive recurrent states, the number of positive recurrent classes making up $R(e)$ does not exceed $|D(e)|$, and there are no null recurrent classes.
--   3. If $e$ is a stationary policy realizing the minimum in the ACOE, then $e\in\Re^*(i,D(e)\cap R(e))$ for all $i$. Hence, if $R(e)$ consists of a single class, then $e$ is $x$ standard for $x\in R(e)$.
--
--   The (BOR) conditions avoid structural properties of $V_\alpha$ and give, besides the ACOE, recurrence properties of every optimal stationary policy.
--
--   **Formalization Note** "The number of positive recurrent classes is at most $|D(e)|$" is stated as: every finite set of pairwise non-communicating positive recurrent states has at most $|D(e)|$ elements (`Set.encard`, so an infinite $D(e)$ is not counted as $0$). "No null recurrent classes" is: every recurrent state is positive recurrent. In part 3, "realizing the minimum in the ACOE" is relative to a limit function $h$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 145, Theorem 7.5.6

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Theorem 7.5.6, p. 145. Assume the (BOR) assumptions hold for `z`, the `z`
standard policy `d` and `ε > 0`. Then, with `J` the (finite, constant) minimum average cost,
`J = lim_{α→1⁻} (1−α)V_α(i)`:
(i) (SEN) holds for `z`, a limit function exists, and the ACOE is valid for every limit function;
(ii) every average cost optimal stationary policy `e` has a positive recurrent state in
`D(e) = {i | C(i,e) ≤ J + ε}`; the number of positive recurrent classes does not exceed `|D(e)|`
(a set of pairwise non-communicating positive recurrent states has at most `|D(e)|` elements);
and there are no null recurrent classes (every recurrent state is positive recurrent);
(iii) if `e` realizes the minimum in the ACOE (for a limit function `h`), then
`e ∈ ℜ*(i, D(e) ∩ R(e))` for all `i`, `R(e)` the set of positive recurrent states; hence if `R(e)`
is a single class, then `e` is `x` standard for every `x ∈ R(e)`. -/
theorem bor_theorem {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (ε : ℝ) (hBOR : BORAssumptions M z d ε) :
    ∃ J : ℝ, 0 ≤ J ∧ (∀ i, avgValue M i = ENNReal.ofReal J) ∧
      (∀ i, Tendsto (fun α : ℝ => ENNReal.ofReal (1 - α) * valueFn M α i) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal J))) ∧
      -- (i)
      (SEN M z ∧ (∃ h : S → ℝ, IsLimitFunction M z h) ∧
        ∀ h : S → ℝ, IsLimitFunction M z h → ACOE M J h) ∧
      -- (ii)
      (∀ e : StationaryPolicy M, IsAvgOptimal e.toPolicy →
        (∃ j ∈ lowCostSetOf M e (ENNReal.ofReal J + ENNReal.ofReal ε),
          PosRecurrent e.toPolicy j) ∧
        (∀ F : Finset S, (∀ j ∈ F, PosRecurrent e.toPolicy j) →
          (∀ j ∈ F, ∀ k ∈ F, j ≠ k → ¬ Communicate e.toPolicy j k) →
          ((F.card : ℕ) : ℕ∞) ≤ (lowCostSetOf M e (ENNReal.ofReal J + ENNReal.ofReal ε)).encard) ∧
        (∀ j, Recurrent e.toPolicy j → PosRecurrent e.toPolicy j)) ∧
      -- (iii)
      (∀ h : S → ℝ, IsLimitFunction M z h → ∀ e : StationaryPolicy M, RealizesMin M h e →
        (∀ i, InRStar e.toPolicy i
          (lowCostSetOf M e (ENNReal.ofReal J + ENNReal.ofReal ε) ∩
            {j | PosRecurrent e.toPolicy j})) ∧
        ((∀ x y, PosRecurrent e.toPolicy x → PosRecurrent e.toPolicy y →
            Communicate e.toPolicy x y) →
          ∀ x, PosRecurrent e.toPolicy x → IsZStandard e.toPolicy x)) := by sorry

end SennottDP.BOR
