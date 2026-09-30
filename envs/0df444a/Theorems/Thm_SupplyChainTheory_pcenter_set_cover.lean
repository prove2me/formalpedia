-- Prove2me | Theorems.Thm_SupplyChainTheory_pcenter_set_cover
-- name    : SupplyChainTheory.pcenter_set_cover
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:42:39.608531+00:00
-- url     : https://prove2.me/theorems/baa062cc-c676-4c8b-b9be-9f79e05e866b
-- title:
--   Lemma 8.8: the $p$-center value is at most $r$ iff the set covering problem with radius $r$ needs at most $p$ facilities
-- statement:
--   **Lemma 8.8.** Let $r \ge 0$ and $1 \le p \le |J|$. The optimal objective value of the
--   (vertex) $p$-center problem is at most $r$ if and only if the optimal objective value of the set
--   covering location problem with coverage radius $r$ is at most $p$, i.e., some set of at most
--   $p$ sites has every customer within distance $r$ of one of its members.
--
--   The book omits the proof (Problem 8.47). A $p$-set with maximum assigned distance at most $r$
--   covers within $r$; a cover with fewer than $p$ sites can be padded to exactly $p$ without
--   increasing any assigned distance. This is the basis of the bisection algorithm for the
--   $p$-center problem, which solves a set covering problem at each radius.
--
--   **Formalization Note** The set covering value is stated through its feasible solutions rather
--   than as a natural-number infimum, whose value on an infeasible instance would be $0$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 312, Sect. 8.4.3, Lemma 8.8: 'Proof. Omitted; see Problem 8.47'

import Definitions.Def_SupplyChainTheory_location

namespace SupplyChainTheory

theorem pcenter_set_cover {n m : ℕ} (c : Fin n → Fin m → ℝ) (p : ℕ) (hp : 1 ≤ p) (hpm : p ≤ m)
    (r : ℝ) (hr : 0 ≤ r) :
    pCenterValue c p ≤ r ↔ ∃ S : Finset (Fin m), S.card ≤ p ∧ ∀ i, ∃ j ∈ S, c i j ≤ r := by sorry

end SupplyChainTheory
