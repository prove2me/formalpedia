-- Prove2me | Theorems.Thm_PayAsBid_SoftReserve_problem_1_well_posed
-- name    : PayAsBid.SoftReserve.problem_1_well_posed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:43.617923+00:00
-- url     : https://prove2.me/theorems/777b9d8d-10ba-42c1-a76a-ad0f218368d8
-- title:
--   §2.2, p. 9 — Problem (1) has a unique solution for every nonempty assortment and nonnegative prices
-- statement:
--   Consider the symmetric affine demand model (Model 2) under the standing assumptions, in particular with $\Gamma$ positive definite. Let $Q\subseteq N$ be a nonempty assortment and $p\in\mathbb R^n_+$ a price vector. Then the consumer's problem
--
--   $$\max_x\ c'x-\tfrac12x'Dx-p'x\quad\text{s.t.}\quad \mathbf 1'x=1,\ x\ge0,\ x_i=0\ \text{for } i\notin Q$$
--
--   has exactly one solution.
--
--   This is what makes the demand $d(Q,p)$, and hence the allocation $x^q(b)=d(q(b),b)$ of every mechanism, a well-defined function.
--
--   **Formalization Note.** "$x$ solves Problem (1)" is the predicate `IsDemand`: $x$ is feasible and $CS(y,p)\le CS(x,p)$ for every feasible $y$.
-- source:
--   Choi, Saban & Weintraub, The Design of Optimal Pay-as-Bid Procurement Mechanisms, SSRN preprint 3785023 (version of 2022-12-08), p. 9 (PDF 9), §2.2, sentence after Problem (1)

import Mathlib
import Definitions.Def_PayAsBid_SoftReserve_Model

namespace PayAsBid.SoftReserve

theorem problem_1_well_posed {n : ℕ} (P : Params n) (hP : P.Standing)
    (Q : Finset (Fin n)) (hQ : Q.Nonempty) (p : Fin n → ℝ) (hp : Nonneg p) :
    ∃! x, IsDemand P Q p x := by sorry

end PayAsBid.SoftReserve
