-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_basicWidthFacts
-- name    : QAlgorithms.Papers.Independent.Information100.P75.basicWidthFacts
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:11:25.976584+00:00
-- url     : https://prove2.me/theorems/a812ddd4-c79a-431b-8277-d800de018d5d
-- title:
--   Five basic numerical-range and width facts
-- statement:
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $n\ge1$ and $A\in M_n(\mathbb C)$. Write $\overline{\operatorname{sw}}(A)=\pi-|\Gamma_A|$ for the overlined width on nonzero matrices, and $\operatorname{Re}A=(A+A^\dagger)/2$. The following five facts hold:
--
--   1. If $0\notin W(A)$, then $A\ne0$ and $\operatorname{sw}(A)=\overline{\operatorname{sw}}(A)<\pi$.
--   2. For every real $\alpha$, $\operatorname{sw}(A)=\operatorname{sw}(e^{i\alpha}A)$.
--   3. For every nonsingular $G$, $\operatorname{sw}(A)=\operatorname{sw}(GAG^\dagger)$.
--   4. One has
--
--   $$[\forall z\in W(A):\operatorname{Re}z\ge0]\iff\operatorname{Re}A\succeq0.$$
--
--   5. If $A\ne0$ and $\overline{\operatorname{sw}}(A)<\pi$, then $\operatorname{Tr}A\ne0$.
--
--   These properties specify the rotation and congruence invariances and the positivity and trace tests used by the paper.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 6, Lemma 9

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Lemma 9, PDF pp.6–7: all five assertions. Overbars occur only on the right of
clause 1 and in clause 5; congruence invariance concerns ordinary width. -/
theorem basicWidthFacts {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (X : Mat ι) :
    (0 ∉ numericalRange X → X ≠ 0 ∧ width X = closedWidth X ∧ width X < Real.pi) ∧
    (∀ a : ℝ, width X = width (phase a • X)) ∧
    (∀ G : Mat ι, IsUnit G.det → width X = width (G * X * Gᴴ)) ∧
    ((∀ z ∈ numericalRange X, 0 ≤ z.re) ↔ (hermitianReal X).PosSemidef) ∧
    (X ≠ 0 → closedWidth X < Real.pi → X.trace ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
