-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_relaxedStatesCompact
-- name    : QAlgorithms.Papers.Independent.Information100.P75.relaxedStatesCompact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:13:19.749031+00:00
-- url     : https://prove2.me/theorems/2ec5718b-3ab8-400b-83e4-d32426b02efb
-- title:
--   Compact convex relaxed states and their overlined width
-- statement:
--   For $0\le\alpha<\pi$, the relaxed-state set consists of the matrices $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\ \operatorname{Tr}(P)+\operatorname{Tr}(Q)=1\}$. Here $P,Q$ are square complex matrices of the indicated dimension; these phase-weighted sums need not be density matrices.
--
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $n\ge1$ and $0\le\alpha<\pi$. The relaxed-state set $\Omega_n(\alpha)$ is nonempty, convex over $\mathbb R$, and compact in the usual finite-dimensional matrix topology. Furthermore,
--
--   $$\rho\in\Omega_n(\alpha)\implies \rho\ne0\ \text{ and }\ \overline{\operatorname{sw}}(\rho)\le\alpha.$$
--
--   The nonzero assertion, explicit in the proof, puts the overlined width in its lawful domain. The compactness supports attainment in the optimization formulation.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 7, Lemma 11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Lemma 11, PDF p.7: nonempty convex compact relaxed states, with nonzero matrices
and the overlined-width bound. Ordinary width would be false for a singular density. -/
theorem relaxedStatesCompact {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    (omega (ι := ι) a).Nonempty ∧ Convex ℝ (omega (ι := ι) a) ∧
    IsCompact (omega (ι := ι) a) ∧
    ∀ R ∈ omega (ι := ι) a, R ≠ 0 ∧ closedWidth R ≤ a := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
