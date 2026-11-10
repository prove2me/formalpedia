-- Prove2me | Theorems.Thm_PrecDTree_Main_claim_4_3
-- name    : PrecDTree.Main.claim_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:50:34.489569+00:00
-- url     : https://prove2.me/theorems/5b015fa2-5e0d-4491-92c7-11d00a822a9c
-- title:
--   Claim 4.3 — for K = OPT(I) the LP (2)–(10) is a relaxation of Partial-RBSC
-- statement:
--   Let $I=(R,B,\mathcal S,t)$ be a feasible Partial-RBSC instance ($|\mathrm{cov}(\mathcal S,B)|\ge t$). For the guess $K=\mathrm{OPT}(I)$ the system (2)–(10) is a relaxation of Partial-RBSC with red-cost bound $\mathrm{OPT}(I)$:
--   $$\text{LP}(\mathrm{OPT}(I))\ \text{is feasible, and every optimal cover } \mathcal S^*\ \text{yields a feasible point with } x_S=\mathbf 1_{S\in\mathcal S^*},\ y_r=\mathbf 1_{r\in\mathrm{cov}(\mathcal S^*,R)} .$$
--   This is the LP the rounding of Theorem 4.2 starts from.
--
--   Differences from the source:
--   - encoding: an integer target t → t : ℕ; reason: a negative target has the same feasible covers, the same OPT (= 0) and the same output condition as t = 0
--   - reading: 'a polynomial-size relaxation of Partial-RBSC with red-cost bound OPT(I)' → on a feasible instance LP(OPT(I)) has a feasible point, and every optimal cover S* yields a feasible point whose x and y are the indicators of S* and of cov(S*, R); reason: a relaxation is a system every (optimal) integral solution satisfies; its size (k + m + n + nm + k² variables) is a property of the definition and is not restated
--   - reading: an instance of Partial-RBSC → hypothesis I.Feasible (|cov(S, B)| ≥ t); reason: OPT(I) exists only on feasible instances
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 10, Claim 4.3

import Mathlib
import Definitions.Def_PrecDTree_Main_RBSC

set_option autoImplicit false

namespace PrecDTree.Main

/-- **Claim 4.3** (p. 10). For the guess `K = OPT(I)` the LP (2)–(10) is a relaxation of
Partial-RBSC with red-cost bound `OPT(I)`: on a feasible instance it has a feasible point, and every
optimal cover `S*` gives one whose `x` and `y` are the indicators of `S*` and of `cov(S*, R)`. -/
theorem claim_4_3 (I : RBInstance) (hI : I.Feasible) :
    (∃ s : LPSol I, LPFeasible I I.opt s) ∧
      ∀ Sstar : Finset (Fin I.m), I.t ≤ (I.blueCov Sstar).card →
        (I.redCov Sstar).card = I.opt →
        ∃ s : LPSol I, LPFeasible I I.opt s ∧ (∀ S, s.x S = if S ∈ Sstar then 1 else 0) ∧
          ∀ r, s.y r = if r ∈ I.redCov Sstar then 1 else 0 := by sorry

end PrecDTree.Main
