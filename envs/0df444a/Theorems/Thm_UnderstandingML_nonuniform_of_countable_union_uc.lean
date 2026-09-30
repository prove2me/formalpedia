-- Prove2me | Theorems.Thm_UnderstandingML_nonuniform_of_countable_union_uc
-- name    : UnderstandingML.nonuniform_of_countable_union_uc
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:47:36.499403+00:00
-- url     : https://prove2.me/theorems/38119845-b10f-4975-a8c5-39d46c3aa85e
-- title:
--   Theorem 7.3: a countable union of classes with the uniform convergence property is nonuniformly learnable
-- statement:
--   **Theorem 7.3.** Let $H$ be a hypothesis class that can be written as a countable union of hypothesis classes, $H = \bigcup_{n \in \mathbb{N}} H_n$, where each $H_n$ enjoys the uniform convergence property. Then $H$ is nonuniformly learnable.
--
--   Formally: for $H = \bigcup_n H_n$ nonempty with each $H_n$ having the uniform convergence property, `NonuniformLearnable loss H` (general loss framework).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §7.1.1 p. 85, Theorem 7.3 (proved in §7.2 via Theorem 7.5)

import Definitions.Def_UnderstandingML_Nonuniform

open MeasureTheory

namespace UnderstandingML

/-- **Theorem 7.3** (p. 85). Let `H` be a hypothesis class that can be written as a countable
union of hypothesis classes, `H = ⋃ₙ Hₙ`, where each `Hₙ` enjoys the uniform convergence
property. Then `H` is nonuniformly learnable. (`H` nonempty, so that a learner with outputs in
`H` exists.) -/
theorem nonuniform_of_countable_union_uc {Z : Type*} [MeasurableSpace Z] {Hyp : Type*}
    (loss : Hyp → Z → ℝ) (Hn : ℕ → Set Hyp) (hne : (⋃ n, Hn n).Nonempty)
    (hUC : ∀ n, HasUniformConvergence loss (Hn n)) :
    NonuniformLearnable loss (⋃ n, Hn n) := by sorry

end UnderstandingML
