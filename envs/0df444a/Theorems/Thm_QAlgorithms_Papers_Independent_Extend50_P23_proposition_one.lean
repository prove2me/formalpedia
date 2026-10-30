-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P23_proposition_one
-- name    : QAlgorithms.Papers.Independent.Extend50.P23.proposition_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:42:26.583491+00:00
-- url     : https://prove2.me/theorems/a7fab571-8a4f-419d-8f45-6a6d803fc3b6
-- title:
--   A fresh projected GUE block detects equivalence and yields a unitary intertwiner
-- statement:
--   Let $\rho:G\to U(n)$ be a continuous representation of a compact Hausdorff group, and let $\mu$ be normalized regular Borel Haar measure. Fix matrices $U\in\mathbb C^{p\times n}$ and $V\in\mathbb C^{q\times n}$ with orthonormal rows whose adjoint ranges are irreducible invariant subspaces. Put $\sigma(g)=U\rho(g)U^\dagger$ and $\tau(g)=V\rho(g)V^\dagger$. After fixing these bases, draw a fresh GUE matrix $H$ and set
--
--   $$
--   X'=\int_G\rho(g)H\rho(g)^\dagger\,d\mu(g),\qquad F=UX'V^\dagger.
--   $$
--
--   With probability one,
--
--   $$
--   F=0\quad\Longleftrightarrow\quad\sigma\text{ and }\tau\text{ are inequivalent}.
--   $$
--
--   For every draw with $F\ne0$, the representations are equivalent, $F$ has a two-sided inverse (in particular $p=q$), and
--
--   $$
--   \sigma(g)=F\tau(g)F^{-1}\quad(g\in G),\qquad
--   \alpha F\text{ is unitary for some }\alpha\in\mathbb C\setminus\{0\}.
--   $$
--
--   This gives both an equivalence test and a change of basis. The GUE draw uses independent real standard normals: if $Z_{ab}=x_{ab}+iy_{ab}$, then $H=(Z+Z^\dagger)/2$. The fixed bases precede the draw; when the bases came from a first random stage, the statement is applied conditionally with a fresh second draw.
-- source:
--   RepLAB: a computational/numerical approach to representation theory, arXiv:1911.09154v1, PDF p. 5, Proposition 1; proof on p.6; sampling law §2.1 on p.4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P23

open MeasureTheory

open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Support21.P09 (EquivalentModels)

open QAlgorithms.Papers.Independent.Dependency50.P05 (UnitaryBetween)

/-- PDF pp.5–6, Proposition 1. Fix the orthonormal bases of two irreducible
invariant subspaces before drawing a fresh GUE matrix as in §2.1, p.4.
Zero detects inequivalence almost surely. Every nonzero block is an invertible
intertwiner, gives the printed similarity, and is a scalar multiple of a unitary.
No floating point threshold is used. -/
theorem proposition_one {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [Measure.IsHaarMeasure mu] [Measure.Regular mu]
    [IsProbabilityMeasure mu] {n p q : ℕ}
    (rho : G → Matrix (Fin n) (Fin n) ℂ) (hrho : IsUnitaryRepresentation rho)
    (U : Matrix (Fin p) (Fin n) ℂ) (V : Matrix (Fin q) (Fin n) ℂ)
    (hU : U * U.conjTranspose = 1) (hV : V * V.conjTranspose = 1)
    (hUinvariant : ∀ g, rho g * U.conjTranspose = U.conjTranspose * rowCompression rho U g)
    (hVinvariant : ∀ g, rho g * V.conjTranspose = V.conjTranspose * rowCompression rho V g)
    (hUirreducible : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (rowCompression rho U))
    (hVirreducible : QAlgorithms.Papers.Independent.Support21.P09.Irreducible (rowCompression rho V)) :
    DetectionLaw (rowCompression rho U) (rowCompression rho V)
      (fun x => U * representationHaarProjection rho mu (gueMatrix x) * V.conjTranspose)
      (gaussianCoordinatesLaw (Fin n)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P23

end
