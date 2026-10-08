-- Prove2me | Theorems.Thm_StabGen_Uniform_uniform_stability_replace_one
-- name    : StabGen.Uniform.uniform_stability_replace_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:10:06.986271+00:00
-- url     : https://prove2.me/theorems/ab3463b8-374a-4017-85ef-27c4e7248c33
-- title:
--   Uniform stability $\beta$ implies replace-one stability $2\beta$
-- statement:
--   Let $A$ be a symmetric learning algorithm with uniform stability $\beta$ at sample size $m$ with respect to the loss $\ell$ (removing any one example changes $\ell(A_S, z)$ by at most $\beta$, for every $z$). Then for every sample $S \in Z^m$, every index $i$, every replacement point $z_i'$ and every $z \in Z$,
--
--   $$|\ell(A_S, z) - \ell(A_{S^i}, z)| \le 2\beta,$$
--
--   where $S^i$ is $S$ with $z_i$ replaced by $z_i'$.
--
--   Stability with respect to the removal of one point thus implies stability with respect to the change of one point. This is the form of stability used in the bounded-differences step of Theorem 12.
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002), p. 504, remark after Definition 6

import Mathlib
import Definitions.Def_FoundationsML_Stability_Loss
import Definitions.Def_StabGen_Hypothesis_Setting
import Definitions.Def_StabGen_Uniform_Stability

open FoundationsML.Stability

namespace StabGen.Uniform

/-- Bousquet & Elisseeff 2002, p. 504 (after Definition 6): an algorithm with uniform stability
`β` at size `m` satisfies `|ℓ(A_S, z) − ℓ(A_{S^i}, z)| ≤ 2β` for every sample `S`, index `i`,
replacement point `z'_i` and point `z`. -/
theorem uniform_stability_replace_one {X Y Y' : Type*} (L : Y' → Y → ℝ)
    (A : StabGen.Hypothesis.LearningAlgorithm X Y Y') (m : ℕ) (β : ℝ) (hstab : HasUniformStability L A m β) :
    ∀ (S : Fin m → X × Y) (i : Fin m) (z' z : X × Y),
      |Loss L (A (StabGen.Hypothesis.trainingSet S)) z - Loss L (A (StabGen.Hypothesis.trainingSet (StabGen.Hypothesis.replaceAt S i z'))) z| ≤ 2 * β := by sorry

end StabGen.Uniform
