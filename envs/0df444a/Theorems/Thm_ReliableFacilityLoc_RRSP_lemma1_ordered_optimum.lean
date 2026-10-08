-- Prove2me | Theorems.Thm_ReliableFacilityLoc_RRSP_lemma1_ordered_optimum
-- name    : ReliableFacilityLoc.RRSP.lemma1_ordered_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:14.416892+00:00
-- url     : https://prove2.me/theorems/59cafc29-407b-4af5-9418-ccfd832c0dbe
-- title:
--   Lemma 1: some optimal split solution uses failure probabilities in nondecreasing order
-- statement:
--   Let $\lambda_i \ge 0$, $0 \le q_j < 1$ for every regular facility $j$, and $R \ge 1$; the costs $d_{ij}$, $\varphi_i$ and multipliers $\mu_{ij}$ have arbitrary signs. Then the split formulation (19a)–(19l) of the relaxed subproblem (RSP$_i$) has an optimal solution $(Y^*, Z^*, P^*, W^*)$ with the following property: for all regular facilities $j$, $k$ and every level $r$ with $r + 1 \le R - 1$,
--
--   $$
--   Z^*_{jr} = 1 \ \text{ and } \ Z^*_{k,r+1} = 1 \quad\Longrightarrow\quad q_j \le q_k .
--   $$
--
--   In words, the failure probabilities that the optimal solution uses on the regular levels are nondecreasing from one level to the next. This is the step of the proof of Proposition 4 that replaces the variable probabilities by ordered ones.
--
--   **Formalization Note** The facilities $j$, $k$ are required to be regular. The printed lemma does not say so, but for $k = J$ (where $q_J = 0$) the conclusion $q_j \le 0$ fails; the proof's assumption "$j, k \le R-1$" is a typo for $j, k \le J - 1$. The existence of an optimal solution is part of the statement (the feasible set is finite and nonempty). The cost and feasibility are those of the split-formulation definition.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 38 (PDF 40), Appendix A.4, Lemma 1

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP
import Definitions.Def_ReliableFacilityLoc_RRSP_Split

open Finset

namespace ReliableFacilityLoc.RRSP

/-- **Lemma 1** (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010), Appendix A.4, p. 38, PDF 40).
Assume `λ_i ≥ 0`, `0 ≤ q_j < 1` and `R ≥ 1`. There is an optimal solution `(Y*, Z*, P*, W*)` of the
split formulation (19a)–(19l) such that, whenever `Z*_jr = 1` and `Z*_{k,r+1} = 1` for regular
facilities `j, k` and `r + 1 ≤ R − 1`, we have `q_j ≤ q_k`: the failure probabilities used at the
levels `0, …, R − 1` are nondecreasing.

Printed: "Lemma 1. There exists an optimal solution (Y∗,Z∗,P∗) to formulation (19a) - (19l), such
that if Z∗jr = 1, Z∗k,r+1 = 1 and r + 1 ≤ R − 1, then qj ≤ qk."

Formalization Note:
1. `j, k` are required to be regular (`j k : Fin J`). The printed statement does not say so, but
   with `k = J` (`q_J = 0`) the conclusion `q_j ≤ 0` fails; the proof's hypothesis
   "j, k ≤ R − 1" is a typo for `j, k ≤ J − 1`.
2. The level `r` is `r.castSucc` and `r + 1` is `r.succ` for `r : Fin R`; `r + 1 ≤ R − 1` is
   `(r : ℕ) + 1 < R`.
3. The split formulation is `IsSplitFeasible` / `splitObjective` (the objective `G` used in the
   proof; see their docstrings). Existence of an optimum is part of the claim: the feasible set is
   finite and nonempty.
4. No sign is assumed on `d`, `φ_i` or `µ`; `λ_i ≥ 0`, `0 ≤ q_j < 1` and `R ≥ 1` are the standing
   assumptions of §3.1 (p. 8). -/
theorem lemma1_ordered_optimum {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (hlam : 0 ≤ lam) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1) (hR : 1 ≤ R) :
    ∃ Y Z P W : Fin (J + 1) → Fin (R + 1) → ℝ,
      IsSplitOptimal lam d phi q mu Y Z P W ∧
        ∀ (j k : Fin J) (r : Fin R), (r : ℕ) + 1 < R →
          Z j.castSucc r.castSucc = 1 → Z k.castSucc r.succ = 1 → q j ≤ q k := by sorry

end ReliableFacilityLoc.RRSP
