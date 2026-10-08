-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_proof_theorem_6d
-- name    : VeinottNoDiscount.Improve.proof_theorem_6d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:47.646726+00:00
-- url     : https://prove2.me/theorems/a1d4e0c8-1a90-4e49-a2c1-06ed6a00e173
-- title:
--   Proof of Theorem 6(d), p. 1290 — g ∈ H(f) ⇒ w(g) > w(f) = 0, or w(g) = w(f) = 0 and z(g) > z(f)
-- statement:
--   Let $f\in F$ and $g\in H(f)$. Then $w(f)=0$ and either
--   $$w(g)>w(f)\qquad\text{or}\qquad w(g)=w(f)\ \text{and}\ z(g)>z(f),$$
--   where $w$ is defined by (10) relative to $f$, $z$ by (12), and $u>v$ means $u\ge v$ coordinatewise with $u\ne v$.
--
--   This is Corollary 1 for the reduced problem with action sets $E(s,f)$ and reward $-y(f)$; with Lemma 4 it yields part (d) of Theorem 6.
--
--   **Formalization Note** Stated in the original model; in Lean $w(g)$ is written $w(f,g)$.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, proof of Theorem 6(d)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Proof of Theorem 6(d).** "Now `g ε H(f) ⊂ E(f)` so we have from Lemma 1 that `x(g) = x(f)`.
It follows from Theorem 5, Lemma 4, and part (c) above that either `w(g) > w(f) = 0` or
`w(g) = w(f) = 0` and `z(g) > z(f)`."

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1290, §3, proof of Theorem 6(d).

This is Theorem 5 and Corollary 1 applied to the reduced problem of the paragraph after Lemma 4
(p. 1289): action sets `E(s, f)`, rewards `−y(f)`, whose improving set is `H(f)`.

**Formalization Note.** Stated in the original model; `>` is `VecGt`. `w M f g` is the paper's
`w(g)` for the fixed `f`; both alternatives of the sentence are kept, and `w(f) = 0` is the first
conjunct. -/
theorem proof_theorem_6d {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    ∀ g ∈ HSet M f, w M f f = 0 ∧
      (VecGt (w M f g) (w M f f) ∨ (w M f g = w M f f ∧ VecGt (z M g) (z M f))) := by sorry

end VeinottNoDiscount.Improve
