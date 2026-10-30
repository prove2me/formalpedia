-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_weylUncertainty
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.weylUncertainty
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:01:03.478273+00:00
-- url     : https://prove2.me/theorems/c43c77dd-596a-46c8-98c2-88962ae0a9eb
-- title:
--   Weyl uncertainty relation
-- statement:
--   Let $d\geq2$, without a primality assumption, and let $\psi$ be a normalized pure $n$-qudit state. Set $\delta=1/(2d)$. If the squared expectations of both $W_x$ and $W_y$ strictly exceed $1-\delta^2$, the Weyl operators commute.
--
--   $$
--   |\langle\psi|W_x|\psi\rangle|^2,|\langle\psi|W_y|\psi\rangle|^2>1-\frac1{4d^2}\ \Longrightarrow\ W_xW_y=W_yW_x.
--   $$
--
--   This gives the source's weyl uncertainty relation in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 24, lemma-3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.24, Lemma 3.10: strict uncertainty thresholds, with delta=1/(2d). -/
theorem weylUncertainty (d n : ℕ) [NeZero d] (hd : 2 ≤ d)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) (hv : ‖v‖ = 1) (x y : DiscretePhaseSpace d n)
    (hx : 1 - (1 / (2 * (d : ℝ))) ^ 2 <
      Complex.normSq (inner ℂ v (QAlgorithms.act (cyclicWeyl d n x) v)))
    (hy : 1 - (1 / (2 * (d : ℝ))) ^ 2 <
      Complex.normSq (inner ℂ v (QAlgorithms.act (cyclicWeyl d n y) v))) :
    cyclicWeyl d n x * cyclicWeyl d n y = cyclicWeyl d n y * cyclicWeyl d n x := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
