-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P35_d_space_structure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P35.d_space_structure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:29:09.273015+00:00
-- url     : https://prove2.me/theorems/5a518951-6728-4925-a0fa-537de626bedb
-- title:
--   Section 4: Banach spaces D_s, bounded subalgebras and D_infinity
-- statement:
--   For every $s>-1$, the norm $|f(\infty)|+\|f\|_{\mathcal D_s,0}$ makes $\mathcal D_s$ a Banach space, but it is not an algebra and can contain unbounded functions. The inclusions of Proposition 4.3 are continuous. In contrast,
--
--   $$\mathcal D_\infty=\bigcup_{s>-1}\mathcal D_s$$
--
--   is an algebra, and $\mathcal D_s^\infty=\mathcal D_s\cap H^\infty(\mathbb C_+)$ is a Banach algebra for $\|f\|_\infty+\|f\|_{\mathcal D_s,0}$. This identifies precisely which symbol spaces support algebra operations.
-- source:
--   Bounded functional calculi for unbounded operators, arXiv:2202.03143v1, PDF p. 20, Section 4: Banach spaces D_s, bounded subalgebras and D_infinity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P35

noncomputable section

open Complex MeasureTheory Filter Set

open scoped Topology ENNReal

namespace QAlgorithms.Papers.Independent.Intakenext100.P35

open QAlgorithms.Papers.Independent.Renew46.P11 (HolomorphicBernstein)

attribute [local instance] Classical.propDecidable

universe u

/-- Section 4: Banach spaces D_s, bounded subalgebras and D_infinity, arXiv:2202.03143v1, PDF page(s) 20. -/
theorem d_space_structure
:
    (∀ s : ℝ, -1 < s → BanachSymbols hp (D s) (dSize s) ∧
      (∃ f g, D s f ∧ D s g ∧ ¬ D s (f * g)) ∧
      BanachAlgebraSymbols hp (DBounded s) (dBoundedSize s)) ∧
    (∀ s sigma : ℝ, -1 < s → s < sigma → ∃ C : ℝ, 0 < C ∧
      ∀ f, D s f → dSize sigma f ≤ ENNReal.ofReal C * dSize s f) ∧
    (∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∀ f, BesovClass f →
      dSize s f ≤ ENNReal.ofReal C * bSize f) ∧
    DUnion 1 ∧
    (∀ f g, DUnion f → DUnion g → DUnion (f + g) ∧ DUnion (f * g)) ∧
    (∀ c : ℂ, ∀ f, DUnion f → DUnion (c • f)) ∧
    (∃ s : ℝ, -1 < s ∧ D s arccot ∧ supSize hp arccot = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P35

end
