-- Prove2me | Theorems.Thm_StrategyProofArrow_WeakGS_theorem_1
-- name    : StrategyProofArrow.WeakGS.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:50.093452+00:00
-- url     : https://prove2.me/theorems/3572ac05-073e-44ec-a8f2-146504fff8eb
-- title:
--   Theorem 1 (Gibbard–Satterthwaite) — a strict voting procedure with ≥ 3 outcomes is strategy-proof iff dictatorial
-- statement:
--   Consider a strict committee: $n\ge 1$ individuals, a finite set $S_m$ of alternatives, and ballots restricted to strong orders (no indifference between distinct alternatives). Let $\nu:\rho_m^n\to S_m$ be a strict voting procedure whose range $T_p=\nu(\rho_m^n)$ contains $p\ge 3$ alternatives (so $m\ge p\ge 3$). Then
--   $$\nu \text{ is strategy-proof} \iff \nu \text{ is dictatorial},$$
--   where dictatorial means that some individual $i$ obtains, at every strict ballot set $C$, the $C_i$-best element of $T_p$.
--
--   This is the Gibbard–Satterthwaite theorem in the form that allows a range smaller than the alternative set: a strategy-proof procedure that never selects some alternatives is still dictatorial on its range ("partially dictatorial"). In the extension to ballots with indifference (Theorem 1′) it is applied to the strict procedure produced by Lemma 9.
--
--   **Formalization Note** Strict ballot sets are `StrongProfile ι A` (functions into the subtype of strong orders), the procedure is a total function on them, and $T_p$ is `Set.range ν`, so $p\ge 3$ is `3 ≤ (Set.range ν).ncard`; $m\ge p$ is automatic for a finite type `A`. The individuals form a finite type `ι` with $1\le |\iota|$. Dictatorial is `StrictDictatorial`: $\nu(C)\,C_i\,y$ for all $y\in T_p$, which for strong orders says $\nu(C)$ is $i$'s top element of $T_p$. This restates the goal of the companion mission on strict committees in this mission's encoding.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Theorem 1, p. 11

import Mathlib
import Definitions.Def_StrategyProofArrow_WeakGS_Basic

namespace StrategyProofArrow.WeakGS

/-- **Theorem 1 (Gibbard–Satterthwaite)** (Satterthwaite, p. 11). For a strict committee with
`n ≥ 1` individuals and `m ≥ p ≥ 3`, where `p` is the number of alternatives in the range of the
strict voting procedure `ν`, `ν` is strategy-proof if and only if it is dictatorial. -/
theorem theorem_1 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (ν : StrictVotingProcedure ι A)
    (hp : 3 ≤ (Set.range ν).ncard) :
    StrictStrategyProof ν ↔ StrictDictatorial ν := by sorry

end StrategyProofArrow.WeakGS
