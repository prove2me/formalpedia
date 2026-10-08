-- Prove2me | Theorems.Thm_RunwayCPS_DiscreteTime_remark_1
-- name    : RunwayCPS.DiscreteTime.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:55.303978+00:00
-- url     : https://prove2.me/theorems/e1350c72-1cc8-4585-9bf6-bc12938e0d46
-- title:
--   Remark 1 — under the triangle inequality, d^min_i = d^max_i = δ_ab
-- statement:
--   Assume $k\ge 1$ and that the separations satisfy the triangle inequality, $\delta_{ac}\le\delta_{ab}+\delta_{bc}$ for all $a,b,c$. Let $i$ be a node of $G$ at a stage $p\ge 2$, with penultimate aircraft $a$ and final aircraft $b$. Then
--   $$
--   d^{\min}_i=d^{\max}_i=\delta_{ab}.
--   $$
--
--   So under the triangle inequality the third coordinate of each node is determined, and the modified network of §6.2 reduces to the discrete-time CPS network of §6.1.2.
--
--   **Formalization Note** Only the first sentence of Remark 1 is formalized here; the equivalence with the §6.1.2 network enters through Lemma 4.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), p. 1660, Remark 1

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork

namespace RunwayCPS.DiscreteTime

/-- Remark 1, first sentence (p. 1660): if the separations satisfy the triangle inequality,
then for every node `i` of `G` at a stage `p ≥ 2`, with penultimate and final aircraft `a`
and `b`, `d^min_i = d^max_i = δ_ab`. -/
theorem remark_1 {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
    (htri : TriangleIneq I.δ) (p : ℕ) (hp : 2 ≤ p) (i : List (Fin n))
    (hi : IsGNode I p i) :
    dmin I i = (I.δ (penult i) (RunwayCPS.Makespan.final i) : ℤ) ∧
      dmax I p i = (I.δ (penult i) (RunwayCPS.Makespan.final i) : ℤ) := by sorry

end RunwayCPS.DiscreteTime
