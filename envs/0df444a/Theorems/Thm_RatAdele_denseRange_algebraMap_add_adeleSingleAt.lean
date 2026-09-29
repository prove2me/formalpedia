-- Prove2me | Theorems.Thm_RatAdele_denseRange_algebraMap_add_adeleSingleAt
-- name    : RatAdele.denseRange_algebraMap_add_adeleSingleAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/85baa03e-82fc-580f-bbe9-df5e30cd1e2a
-- title:
--   Strong approximation for ℚ away from one finite place
-- statement:
--   Let $v$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, that is, a nonzero prime ideal of $\mathcal{O}_{\mathbb{Q}}$, and let $v.\mathrm{adicCompletion}\ \mathbb{Q}$ be the completion of $\mathbb{Q}$ at $v$. Consider the map from $\mathbb{Q} \times v.\mathrm{adicCompletion}\ \mathbb{Q}$ to the adele ring $\mathrm{AdeleRing}(\mathcal{O}_{\mathbb{Q}}, \mathbb{Q})$, the product of the infinite adele ring of $\mathbb{Q}$ with the finite adele ring (the restricted product of the completions $v.\mathrm{adicCompletion}\ \mathbb{Q}$ with respect to the subrings of integers $v.\mathrm{adicCompletionIntegers}\ \mathbb{Q}$), sending a pair $(q, y)$ to the sum of the image of $q$ under the canonical algebra map $\mathbb{Q} \to \mathrm{AdeleRing}(\mathcal{O}_{\mathbb{Q}}, \mathbb{Q})$ and of $\mathrm{adeleSingleAt}\ \mathbb{Q}\ v\ y$, the adele whose infinite component is $0$ and whose finite component is the restricted-product element $\mathrm{RestrictedProduct.single}$ concentrated at $v$, namely $y$ in the coordinate at $v$ and $0$ in every other coordinate. The assertion is that this map has dense range: every nonempty open subset of the adele ring of $\mathbb{Q}$ contains an element of the form $\Delta(q) + \iota_v(y)$ with $q \in \mathbb{Q}$ and $y$ in the completion at $v$.
--
--   This is the strong approximation theorem for $\mathbb{Q}$ with the single finite place $v$ removed, in the equivalent form that principal adeles together with adeles supported at $v$ are dense in the full adele ring. It is used in the analysis of adelic automorphic forms, being cited by [`AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous`](thm.html#AutomorphicForm.SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous) and by [`LanglandsTunnell.CubicInduction.mirabolicSeries_eq_dual_of_radicalCoefficient_eq`](thm.html#LanglandsTunnell.CubicInduction.mirabolicSeries_eq_dual_of_radicalCoefficient_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RatAdele_denseRange_algebraMap_add_adeleSingleAt.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RatAdele.denseRange_algebraMap_add_adeleSingleAt
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    DenseRange fun qy : ℚ × v.adicCompletion ℚ =>
      algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) qy.1 +
        NumberField.StandardAddChar.adeleSingleAt ℚ v qy.2 := by sorry
