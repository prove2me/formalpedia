-- Prove2me | Theorems.Thm_SkutellaCQP_RelDates_zqp_slotInd
-- name    : SkutellaCQP.RelDates.zqp_slotInd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:12:30.110977+00:00
-- url     : https://prove2.me/theorems/a5b158ee-5958-488f-8c36-13e90c6fa996
-- title:
--   §3.2, p. 17 — for 0/1 slot assignments the relaxed objective (19) equals the objective with (17)
-- statement:
--   Let $\tau$ be any assignment of jobs to time slots and $a$ its 0/1 vector ($a_{i_kj} = 1$ iff $\tau(j) = i_k$). Then the objective of the quadratic programming relaxation at $a$, with completion times (19) and slot starts (15)–(16), equals the objective of the integer program, with completion times (17):
--   $$\sum_j w_j \sum_{i,k} a_{i_kj}\Big(s_{i_k} + \frac{1 + a_{i_kj}}{2}p_{ij} + \sum_{j' \prec_i j} a_{i_kj'}p_{ij'}\Big) = \sum_j w_j\Big(s_{\tau(j)} + p_{ij} + \sum_{j' \prec_i j,\ \tau(j') = \tau(j)} p_{ij'}\Big).$$
--
--   This is why the quadratic program is a relaxation: for integral $a$ the factor $(1 + a_{i_kj})/2$ equals $1$, and the right-hand side of (17) "is the sum of these expressions over all time slots $i_k$ weighted by $a_{i_kj}$; it is thus equal to the completion time of $j$".
--
--   **Formalization Note.** Stated for every slot assignment, feasible or not; standing assumptions are hypotheses.
-- source:
--   Skutella, Convex quadratic and semidefinite programming relaxations in scheduling, J. ACM 48 (2001), p. 17, §3.2, paragraph after (14)–(18), and (19)

import Mathlib
import Definitions.Def_SkutellaCQP_RelDates_Setting

namespace SkutellaCQP.RelDates

open Finset

/-- p. 17: for a 0/1 slot assignment, the objective of the quadratic programming relaxation
(with (19)) equals the objective with the completion times (17). -/
theorem zqp_slotInd {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ) (r : Fin m → Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (hr : ∀ i j, 0 ≤ r i j)
    (τ : Fin n → Fin m × Fin n) :
    ZQPrel p w r (slotInd τ) = ∑ j, w j * Cslot p w r τ j := by sorry

end SkutellaCQP.RelDates
