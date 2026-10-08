-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_theorem_6
-- name    : VeinottNoDiscount.Improve.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:10.759421+00:00
-- url     : https://prove2.me/theorems/fdb0fea9-6f20-4e82-90a7-dc64486ea4b4
-- title:
--   Theorem 6 — G(f) ∪ H(f) empty ⇒ f ∈ F″; improvement steps raise (x, y, z) lexicographically
-- statement:
--   In Blackwell's finite decision model without discounting, let $x(f)$ and $y(f)$ be the gain and bias of the stationary policy $f^\infty$, let $z(f)$ be the unique solution of $[I-Q(f)]z=-y(f)$, $Q^*(f)z=0$, and let $G(f)$, $H(f)$ be Veinott's improvement sets. For vectors, $u>v$ means $u\ge v$ coordinatewise and $u\ne v$. Suppose $f\in F$. Then
--
--   1. if $G(f)$ is empty, then $f\in F'$;
--   2. if $G(f)\cup H(f)$ is empty, then $f\in F''$;
--   3. if $g\in G(f)$, then either $x(g)>x(f)$, or $x(g)=x(f)$ and $y(g)>y(f)$;
--   4. if $g\in H(f)$, then $x(g)=x(f)$, and either $y(g)>y(f)$, or $y(g)=y(f)$ and $z(g)>z(f)$.
--
--   In short,
--   $$G(f)\cup H(f)=\varnothing\ \Longrightarrow\ f\in F'',$$
--   and every step $f\mapsto g\in G(f)\cup H(f)$ raises the triple $(x,y,z)$ lexicographically, so the extended policy improvement method cannot cycle and stops, after finitely many steps, at a decision rule $f$ with $f^\infty$ 1-optimal (Theorem 4).
--
--   **Formalization Note** Every action is available in every state. $G(f)$, $H(f)$, $F'$, $F''$ are sets of decision rules defined literally from the paper's inequalities (i)–(iii); $z(f)$ is the closed form $H(f)(-y(f))$ with Blackwell's deviation matrix.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, Theorem 6

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Theorem 6.** Suppose `f ε F`.
(a) If `G(f)` is empty, then `f ε F′`.
(b) If `G(f) ∪ H(f)` is empty, then `f ε F″`.
(c) If `g ε G(f)`, then either `x(g) > x(f)`, or `x(g) = x(f)` and `y(g) > y(f)`.
(d) If `g ε H(f)`, then `x(g) = x(f)`; and either `y(g) > y(f)`, or `y(g) = y(f)` and
`z(g) > z(f)`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, Theorem 6.

**Formalization Note.** `F = St → Act` (`A_s = Act` for every state). `G(f)`, `H(f)`, `F′`,
`F″` are `GSet`, `HSet`, `Fprime`, `Fdprime` (sets of decision rules; `HSet` is not Blackwell's
deviation matrix `Hf`). `x`, `y` are Blackwell's gain and bias `Q*(f)r(f)`, `H(f)r(f)`; `z` is
`H(f)(−y(f))`, the unique solution of (12). `>` is `VecGt` (`≧` and `≠`). -/
theorem theorem_6 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    (GSet M f = ∅ → f ∈ Fprime M) ∧
      (GSet M f ∪ HSet M f = ∅ → f ∈ Fdprime M) ∧
      (∀ g ∈ GSet M f, VecGt (M.x g) (M.x f) ∨ (M.x g = M.x f ∧ VecGt (M.y g) (M.y f))) ∧
      (∀ g ∈ HSet M f, M.x g = M.x f ∧
        (VecGt (M.y g) (M.y f) ∨ (M.y g = M.y f ∧ VecGt (z M g) (z M f)))) := by sorry

end VeinottNoDiscount.Improve
