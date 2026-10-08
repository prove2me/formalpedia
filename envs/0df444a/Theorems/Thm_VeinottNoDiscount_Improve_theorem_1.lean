-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_theorem_1
-- name    : VeinottNoDiscount.Improve.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:33.876995+00:00
-- url     : https://prove2.me/theorems/91948aec-eae5-4fe7-96a3-bf6e9a514297
-- title:
--   Theorem 1 (Blackwell) — exactly one: f^∞ is β-optimal with no one-step improvement, or some g has V_β(g, f^∞) > V_β(f^∞) and V_β(g^∞) > V_β(f^∞)
-- statement:
--   Fix a decision rule $f\in F$ and a discount factor $0\le\beta<1$. Write $V_\beta(\pi)$ for the vector of expected total discounted returns of a policy $\pi$, $f^\infty$ for the stationary policy using $f$ every period, and $(g,f^\infty)$ for the policy that uses $g$ in the first period and $f$ thereafter. For vectors, $u\ge v$ means $u_s\ge v_s$ for all $s$, and $u>v$ means $u\ge v$ and $u\ne v$. Then exactly one of the following holds:
--
--   1. $V_\beta(f^\infty)\ge V_\beta(g,f^\infty)$ for all $g\in F$, and $f^\infty$ is $\beta$-optimal ($V_\beta(f^\infty)\ge V_\beta(\pi)$ for every policy $\pi$);
--   2. there is $g\in F$ with
--   $$V_\beta(g,f^\infty)>V_\beta(f^\infty)\quad\text{and}\quad V_\beta(g^\infty)>V_\beta(f^\infty).$$
--
--   This is the policy improvement method for a fixed discount factor: either $f^\infty$ cannot be improved in one step and is then optimal, or a one-step improvement yields a strictly better stationary policy.
--
--   **Formalization Note** One and the same $g$ witnesses both inequalities in the second alternative. The strict order is not coordinatewise strict.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1285, Theorem 1

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Theorem 1 (Blackwell).** Exactly one of the following must occur for each `f ε F` and
`0 ≦ β < 1`:
(a) `V_β(f^∞) ≧ V_β(g, f^∞)` for all `g ε F` and `f^∞` is β-optimal.
(b) `V_β(f^∞) < V_β(g, f^∞)` for some `g ε F` and `V_β(f^∞) < V_β(g^∞)`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1285, Theorem 1.

**Formalization Note.** `u < v` is the paper's vector order (`v ≧ u` and `v ≠ u`), i.e.
`VecGt v u`, not coordinatewise strict. In (b) one `g` witnesses both inequalities (the
improving decision rule of the policy improvement method). `(g, f^∞)` is
`Policy.cons g (Policy.stationary f)`; β-optimal is the published `IsBetaOptimal` (comparison
with every policy). `Xor` expresses "exactly one". -/
theorem theorem_1 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Xor
      ((∀ g : St → Act,
          M.V β (Policy.cons g (Policy.stationary f)) ≤ M.V β (Policy.stationary f)) ∧
        M.IsBetaOptimal β (Policy.stationary f))
      (∃ g : St → Act,
        VecGt (M.V β (Policy.cons g (Policy.stationary f))) (M.V β (Policy.stationary f)) ∧
          VecGt (M.V β (Policy.stationary g)) (M.V β (Policy.stationary f))) := by sorry

end VeinottNoDiscount.Improve
