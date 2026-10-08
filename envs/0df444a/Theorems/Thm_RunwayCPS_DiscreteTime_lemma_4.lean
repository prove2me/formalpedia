-- Prove2me | Theorems.Thm_RunwayCPS_DiscreteTime_lemma_4
-- name    : RunwayCPS.DiscreteTime.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:33.354281+00:00
-- url     : https://prove2.me/theorems/f9cdb2e9-abbe-40dc-91b9-b4005265f1c7
-- title:
--   Lemma 4 — under the triangle inequality, a feasible schedule exists iff the discrete-time CPS network has a source-sink path
-- statement:
--   Assume the separations satisfy the triangle inequality. Then a feasible schedule (respecting the CPS constraints, the precedence requirements, the time windows and the separations) exists if and only if the discrete-time CPS network of §6.1.2 has a source-sink path:
--   $$
--   \exists\,(\sigma,t)\ \text{feasible}\iff \exists\ \text{source-sink path } (i_1,t_1)\to\dots\to(i_n,t_n).
--   $$
--
--   This is the correctness statement behind the dynamic program (2)–(3) of §6.1.1 when the triangle inequality holds; the absence of a path proves infeasibility.
--
--   **Formalization Note** The paper omits the proof and says it follows from the proof of Lemma 5 via Remark 1.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1657, Lemma 4; p. 1660, Remark 1

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_DTNetwork

namespace RunwayCPS.DiscreteTime

/-- Lemma 4 (p. 1657): if the separations satisfy the triangle inequality, a feasible schedule
exists if and only if the discrete-time CPS network of §6.1.2 (Figure 3) has a source-sink
path. -/
theorem lemma_4 {n : ℕ} [NeZero n] (I : Instance n) (htri : TriangleIneq I.δ) :
    (∃ (σ : Fin n → Fin n) (t : Fin n → ℕ), IsFeasible I σ t) ↔
      ∃ P : ℕ → TNode n, IsTPath I P := by sorry

end RunwayCPS.DiscreteTime
