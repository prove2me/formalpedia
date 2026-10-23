-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_annihilatorObstruction
-- name    : QAlgorithms.Papers.Independent.Information100.P75.annihilatorObstruction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:14:00.578827+00:00
-- url     : https://prove2.me/theorems/71cf52bc-0569-448f-9207-b688fc4c67e4
-- title:
--   Width obstruction and relaxed annihilator existence
-- statement:
--   For $0\le\alpha<\pi$, the relaxed-state set consists of the matrices $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\ \operatorname{Tr}(P)+\operatorname{Tr}(Q)=1\}$. Here $P,Q$ are square complex matrices of the indicated dimension; these phase-weighted sums need not be density matrices.
--
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $n\ge1$ and $A\in M_n(\mathbb C)$. Every nonzero matrix $X$ with $\operatorname{Tr}(XA)=0$ satisfies
--
--   $$\overline{\operatorname{sw}}(X)\ge\pi-\operatorname{sw}(A).$$
--
--   If $\operatorname{sw}(A)>0$, then for every real $\alpha$ with $\pi-\operatorname{sw}(A)\le\alpha<\pi$ there exists $\rho\in\Omega_n(\alpha)$ with $\operatorname{Tr}(\rho A)=0$. This relates annihilation to the two distinct width notions and includes the lower endpoint of the existence interval.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 7, Lemma 12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Lemma 12, PDF pp.7–8: nonzero annihilator obstruction (overlined width), and
existence at every angle in the half-open interval, including its lower endpoint. -/
theorem annihilatorObstruction {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (X : Mat ι) :
    (∀ Y : Mat ι, Y ≠ 0 → (Y * X).trace = 0 → Real.pi - width X ≤ closedWidth Y) ∧
    (0 < width X → ∀ a : ℝ, Real.pi - width X ≤ a → a < Real.pi →
      ∃ R ∈ omega (ι := ι) a, (R * X).trace = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
