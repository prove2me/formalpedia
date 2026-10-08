-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_xOfCut_injOn
-- name    : ProjSchedMinCut.Transform.xOfCut_injOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:48.811978+00:00
-- url     : https://prove2.me/theorems/64268cac-a1b2-44fb-81bf-ff1e5bcba532
-- title:
--   p. 8, after Lemma 2 — the mapping (7) is injective on finite-capacity n-cuts
-- statement:
--   Let $D$ be the minimum cut digraph of an instance of the project scheduling problem with start-time dependent costs $w_{jt} \ge 0$, and assume a feasible schedule exists. If two $n$-cuts $(X, \bar X)$ and $(Y, \bar Y)$ of $D$, both of finite capacity, have the same image under the mapping (7),
--   $$x_{jt} = \begin{cases} 1 & \text{if } (v_{jt}, v_{j,t+1}) \text{ is in the cut},\\ 0 & \text{otherwise,}\end{cases}$$
--   then $X = Y$.
--
--   This is the injectivity half of the one-to-one correspondence of Theorem 1, which the paper says "follows by definition".
--
--   **Formalization Note** Cuts are represented by the source side $X \subseteq V$, so equal cuts means $X = Y$.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 8, the sentence after the proof of Lemma 2

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- p. 8, after the proof of Lemma 2: the mapping (7) is injective on the `n`-cuts of `D` of
finite capacity. -/
theorem xOfCut_injOn {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    Set.InjOn I.xOfCut {X | I.IsNCut X ∧ I.cutCap X < ⊤} := by sorry

end ProjSchedMinCut.Transform
