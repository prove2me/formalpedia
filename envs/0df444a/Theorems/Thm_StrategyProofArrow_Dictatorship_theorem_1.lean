-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_theorem_1
-- name    : StrategyProofArrow.Dictatorship.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:11.223729+00:00
-- url     : https://prove2.me/theorems/2600ba12-0967-43c7-9ebe-188e7b6da81e
-- title:
--   Theorem 1 (Gibbard–Satterthwaite) — a strict voting procedure with at least three possible outcomes is strategy-proof iff it is dictatorial
-- statement:
--   Consider a strict committee $\langle I_n,S_m,v^{nm},T_p\rangle$: $n\ge 1$ individuals, $m$ alternatives, every preference and every ballot a strong order, and a strict voting procedure $v^{nm}$ whose range $T_p$ has $p$ elements, with $m\ge p\ge 3$. Then
--
--   $$v^{nm}\ \text{is strategy-proof}\iff v^{nm}\ \text{is dictatorial},$$
--
--   where dictatorial means that some individual $i$ exists such that, at every strict ballot set $B\in\rho^n_m$, $v^{nm}(B)$ is the alternative of the range $T_p$ that $B_i$ ranks highest.
--
--   The dictatorship is relative to the range: when $T_p\subsetneq S_m$ the dictator obtains their best alternative among those the procedure can select, not their best alternative overall (a partial dictatorship). With $T_p=S_m$ the theorem is the classical Gibbard–Satterthwaite theorem. The bound $p\ge 3$ cannot be lowered: with two possible outcomes, majority voting between them is strategy-proof and not dictatorial.
--
--   **Formalization Note** $n=$ `Fintype.card ι`, $p=$ `(range f).ncard`, where `range f` collects the values of `f` at strict ballot sets only. $m\ge p$ holds automatically, so $m\ge 3$ follows from $p\ge 3$ and is not a separate hypothesis. Strategy-proofness is `AGT.IncentiveCompatible`. The paper's dictator function $f^i_T$ is any single-valued selection from $i$'s maximal elements of $T_p$; for strict ballots that element is unique, and `Dictatorial f` says that $f(B)$ is it.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Theorem 1, p. 11

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Theorem 1 (Gibbard–Satterthwaite)** (Satterthwaite, p. 11). For a strict committee with
`n ≥ 1` individuals whose strict voting procedure has a range `T_p` of `p ≥ 3` alternatives
(so `m ≥ p ≥ 3`), the procedure is strategy-proof if and only if it is dictatorial: some
individual always obtains their most preferred alternative of the range. -/
theorem theorem_1 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι)
    (f : (ι → A → A → Prop) → A) (hp : 3 ≤ (range f).ncard) :
    IncentiveCompatible f ↔ Dictatorial f := by sorry

end StrategyProofArrow.Dictatorship
