-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_lemma_4
-- name    : VeinottNoDiscount.Improve.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:18.724515+00:00
-- url     : https://prove2.me/theorems/71bdda11-7d3d-4d14-826a-12d11b62ac4d
-- title:
--   Lemma 4 — for g ∈ E(f), y(g) = y(f) + w(g) with w(g) the unique solution of (10)
-- statement:
--   Let $f\in F$ and $g\in E(f)$, the set of decision rules for which the gain and bias tests (i), (ii) hold with equality at every state. Then the system
--   $$[I-Q(g)]\,w=0,\qquad Q^*(g)\,w=Q^*(g)\,(-y(f))\tag{10}$$
--   has exactly one solution $w(g)$, and
--   $$y(g)=y(f)+w(g).\tag{11}$$
--
--   The lemma turns the maximization of the bias over $E(f)$ into the maximization of a gain-type quantity, $w(g)$, which has the same form as the original gain maximization with reward $-y(f)$.
--
--   **Formalization Note** $w(g)$ is defined as $Q^*(g)(-y(f))$; the statement asserts that this vector is the one and only solution of (10).
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1289, Lemma 4, (10), (11)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Lemma 4.** Suppose `f ε F` and `g ε E(f)`. Let `w(g)` be the unique solution to
(10) `[I − Q(g)]w = 0, Q*(g)w = Q*(g)(−y(f))`. Then (11) `y(g) = y(f) + w(g)`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1289, Lemma 4, (10), (11).

**Formalization Note.** `w M f g` is the closed form `Q*(g)(−y(f))`; the first conjunct says it is
the one and only solution of (10) (the paper's "unique solution"), the second is (11). -/
theorem lemma_4 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f g : St → Act) (hg : g ∈ ESet M f) :
    (∀ v : St → ℝ,
        ((1 - M.Q g) *ᵥ v = 0 ∧ M.Qstar g *ᵥ v = M.Qstar g *ᵥ (-(M.y f))) ↔ v = w M f g) ∧
      M.y g = M.y f + w M f g := by sorry

end VeinottNoDiscount.Improve
