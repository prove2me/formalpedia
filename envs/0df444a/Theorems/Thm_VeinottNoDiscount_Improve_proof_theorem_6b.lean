-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_proof_theorem_6b
-- name    : VeinottNoDiscount.Improve.proof_theorem_6b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:49.771561+00:00
-- url     : https://prove2.me/theorems/10fad740-3827-4f8e-a049-1a007ae38586
-- title:
--   Proof of Theorem 6(b), p. 1290 — w(f) = 0, and H(f) empty ⇒ y(g) ≤ y(f) for all g ∈ E(f)
-- statement:
--   Let $f\in F$ and, for $g\in E(f)$, let $w(g)$ be the unique solution of (10). Then $w(f)=0$, and if $H(f)$ is empty,
--   $$y(g)\le y(f)\qquad\text{for all } g\in E(f).$$
--
--   This is the step of the proof of Theorem 6(b) that combines Lemma 4 with Theorem 5 applied to the reduced problem with action sets $E(s,f)$ and reward $-y(f)$, whose improving set is $H(f)$; Lemma 5 then gives $f\in F''$.
--
--   **Formalization Note** The reduced problem is not instantiated: the published model has one action set for all states. The statement records the consequence in the original model. In Lean $w(g)$ is written $w(f,g)$, so $w(f)$ is $w(f,f)$.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, proof of Theorem 6(b) (with the paragraph after Lemma 4, p. 1289)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Proof of Theorem 6(b), first step.** "First note from (11) that `w(f) = 0`. Thus since `H(f)`
is empty, it follows from Theorem 5 and Lemma 4 that `y(g) ≦ y(f)` for all `g ε E(f)`."

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, proof of Theorem 6(b).

The reason is the paragraph after Lemma 4 (p. 1289): "Notice from (2), (8), and Lemma 4 that the
problem of maximizing w(g) over g ε E(f) has the same form as that of maximizing x(g) over g ε F
where we replace A_s by E(s, f), F by E(f), and r(g) by −y(f) for s = 1, ⋯ , S and all g ε E(f).
Thus the policy improvement method of Theorem 5 can be used to find an h that maximizes w(g)—and
hence y(g) in view of (11)—over g ε E(f)."

**Formalization Note.** Stated in the original model (Blackwell's `Model` has one action set for
all states, so the reduced problem with action sets `E(s, f)` is not instantiated). `w M f f` is
the paper's `w(f)` (with the paper's `f` fixed). Only `H(f) = ∅` is assumed, as in the
sentence; `G(f) = ∅` is used afterwards, through Lemma 5. -/
theorem proof_theorem_6b {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    w M f f = 0 ∧ (HSet M f = ∅ → ∀ g ∈ ESet M f, M.y g ≤ M.y f) := by sorry

end VeinottNoDiscount.Improve
