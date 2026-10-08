-- Prove2me | Theorems.Thm_VeinottNoDiscount_Improve_lemma_5
-- name    : VeinottNoDiscount.Improve.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:00.089288+00:00
-- url     : https://prove2.me/theorems/beea6b89-0fde-4b03-96c4-f2080a6d9108
-- title:
--   Lemma 5 — G(f) empty and y(f) ≥ y(g) for all g ∈ E(f) ⇒ f ∈ F″
-- statement:
--   Let $f\in F$. If $G(f)$ is empty and
--   $$y(f)\ge y(g)\qquad\text{for all } g\in E(f),$$
--   then $f\in F''$: $f$ has maximal gain and, among the decision rules of maximal gain, maximal bias.
--
--   The lemma is the certificate that lets the algorithm stop: it suffices to maximize the bias over the explicitly available set $E(f)$ instead of over $F'$, which is hard to describe.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1289, Lemma 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Improve_Sets
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Improve

/-- **Lemma 5.** If `f ε F`, if `G(f)` is empty, and if `y(f) ≧ y(g)` for all `g ε E(f)`, then
`f ε F″`.

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1289, Lemma 5.

**Formalization Note.** `G(f)`, `E(f)`, `F″` are `GSet`, `ESet`, `Fdprime`; `≧` is pointwise. -/
theorem lemma_5 {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) (hG : GSet M f = ∅) (hy : ∀ g ∈ ESet M f, M.y g ≤ M.y f) :
    f ∈ Fdprime M := by sorry

end VeinottNoDiscount.Improve
