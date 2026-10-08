-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakGS_theorem_1_prime
-- name    : StrategyProofArrow.WeakGS.theorem_1_prime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:20.403927+00:00
-- url     : https://prove2.me/theorems/8d3d1d28-37cf-43bd-ac01-0db21280589c
-- title:
--   Theorem 1′ — with indifference allowed, a strategy-proof voting procedure with ≥ 3 outcomes is dictatorial
-- statement:
--   Consider a committee of $n\ge 2$ individuals and a finite set $S_m$ of alternatives in which every weak order (indifference allowed) is an admissible ballot. Let $v:\pi_m^n\to S_m$ be a voting procedure whose range $T_p=v(\pi_m^n)$ contains $p\ge 3$ alternatives (so $m\ge p\ge 3$). If $v$ is strategy-proof, then $v$ is dictatorial: there is an individual $i$ such that
--   $$v(B)\;B_i\;y\qquad\text{for every ballot set } B\in\pi_m^n \text{ and every } y\in T_p,$$
--   that is, $v(B)$ is always among $i$'s most preferred elements of the range.
--
--   This is the extension of the Gibbard–Satterthwaite theorem to ballots with indifference. Only the "only if" direction holds: a dictator's ties may be broken by a manipulable rule (for instance a Borda count of the other ballots), so a dictatorial procedure need not be strategy-proof once indifference is admissible.
--
--   **Formalization Note** Ballot sets are `WeakProfile ι A` and the procedure is a total function on them, so $T_p$ is `Set.range v` and $p\ge 3$ is `3 ≤ (Set.range v).ncard`; $m\ge p$ is automatic for a finite type `A`. Strategy-proofness compares outcomes by the *strict* part $\bar B_i$ of the true ballot and allows any weak order as the substituted ballot. The paper defines dictatorship through a function $f^i_T$ that picks, with an unspecified tie-break, a $B_i$-maximal element of $T_p$; we state the equivalent condition that $v(B)$ is $B_i$-maximal in $T_p$, without fixing the tie-break. $n\ge 2$ is as printed.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Theorem 1', p. 43

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Theorem 1'** (Satterthwaite, p. 43). Consider a committee in which indifference is admissible
on ballots, with `n ≥ 2` individuals and `m ≥ p ≥ 3`, where `p` is the number of alternatives in the
range `T_p` of the voting procedure `v` over all ballot sets `π^n_m`. If `v` is strategy-proof, then
it is dictatorial. -/
theorem theorem_1_prime {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (v : VotingProcedure ι A)
    (hp : 3 ≤ (Set.range v).ncard) :
    StrategyProof v → Dictatorial v := by sorry

end StrategyProofArrow.WeakGS
