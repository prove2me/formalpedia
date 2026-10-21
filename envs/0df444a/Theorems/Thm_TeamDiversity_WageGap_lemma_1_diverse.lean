-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_lemma_1_diverse
-- name    : TeamDiversity.WageGap.lemma_1_diverse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:05.336229+00:00
-- url     : https://prove2.me/theorems/d2e4b1a9-2998-4345-8fa4-3d6af963dc75
-- title:
--   Lemma 1 (k = d), p. 12 — the optimal diverse mutual-monitoring wage is w_d* = c/((1−δ)(f_d(2)−f_d(1)) + δ(f_d(2)−f_d(0)))
-- statement:
--   Under the standing assumptions of the model, fix a discount factor $\delta \in [0,1]$. Among all diverse wages $w_d \ge 0$ satisfying (IR) $f_d(2)w_d - c \ge 0$ and (M-IC) $f_d(2)w_d - c \ge (1-\delta)f_d(1)w_d + \delta f_d(0)w_d$, the least one is
--
--   $$w_d^* = \frac{c}{(1-\delta)\big(f_d(2)-f_d(1)\big) + \delta\big(f_d(2)-f_d(0)\big)}.$$
--
--   This is the diverse half of Lemma 1: the principal's optimal mutual-monitoring contract for a diverse team, sustained by the (shirk, shirk) punishment.
--
--   **Formalization Note** "Optimal contract" is encoded as the least element of the feasible set, since the principal's objective is decreasing in the wage.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 12 (PDF 13), Lemma 1 (case k = d); program 2) of Appendix A, p. 31 (PDF 32)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Lemma 1 (k = d), p. 12: the optimal mutual-monitoring wage of a diverse team. -/
theorem lemma_1_diverse (c : ℝ) (fs fd : Tech) (hst : Standing c fs fd) :
    ∀ δ ∈ Set.Icc (0 : ℝ) 1,
      IsLeast (FeasD c fd δ) (c / ((1 - δ) * (fd.f2 - fd.f1) + δ * (fd.f2 - fd.f0))) := by sorry

end TeamDiversity.WageGap
