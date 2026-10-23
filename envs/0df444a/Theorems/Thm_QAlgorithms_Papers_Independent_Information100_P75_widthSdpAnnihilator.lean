-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_widthSdpAnnihilator
-- name    : QAlgorithms.Papers.Independent.Information100.P75.widthSdpAnnihilator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:07:56.207532+00:00
-- url     : https://prove2.me/theorems/231d0536-374a-47b4-8e4b-bfd1931ad69e
-- title:
--   Width, SDP zero and a common annihilator
-- statement:
--   For $0\le\alpha<\pi$, the relaxed-state set consists of the matrices $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\ \operatorname{Tr}(P)+\operatorname{Tr}(Q)=1\}$. Here $P,Q$ are square complex matrices of the indicated dimension; these phase-weighted sums need not be density matrices.
--
--   For a square complex matrix $X$, $W(X)$ denotes its numerical range, equivalently the values $\operatorname{Tr}(\sigma X)$ over PSD matrices $\sigma$ of trace one. Put $\Gamma_X=\{\theta\in[-\pi,\pi):\operatorname{Re}(e^{i\theta}X)\succeq0\}$, where $\operatorname{Re}Y=(Y+Y^\dagger)/2$, with Lebesgue length $|\Gamma_X|$ in radians. The ordinary width is $\operatorname{sw}(X)=\pi$ when $0\in W(X)$ and $\pi-|\Gamma_X|$ otherwise. For a complex subspace $\mathcal M$, $\operatorname{sw}^*(\mathcal M)=\inf_{X\in\mathcal M}\operatorname{sw}(X)$. The overlined width of a nonzero matrix is $\overline{\operatorname{sw}}(X)=\pi-|\Gamma_X|$.
--
--   Let $n\ge1$, let $\mathcal A\subset M_n(\mathbb C)$ be a complex linear subspace, and let $0\le\alpha<\pi$. Write $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\operatorname{Tr}P+\operatorname{Tr}Q=1\}$. For a basis $(A_l)_{l=1}^k$ of $\mathcal A$, let $D_\alpha$ be the minimum of $\sum_l|\operatorname{Tr}(\rho A_l)|$ over this set. Then
--
--   $$
--   \operatorname{sw}^*(\mathcal A)+\alpha\ge\pi
--   \iff [D_\alpha(A_1,\ldots,A_k)=0\text{ for every basis}]
--   \iff \exists\rho\in\Omega_n(\alpha)\ \forall A\in\mathcal A:\operatorname{Tr}(\rho A)=0.
--   $$
--
--   This links the geometric width, the optimization problem and a single common trace annihilator.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 3, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Theorem 2, PDF pp.3–4: all three conditions, universally over finite bases.
The zero-dimensional subspace has its empty basis; no attainment premise is imposed. -/
theorem widthSdpAnnihilator {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule ℂ (Mat ι)) (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    ((Real.pi ≤ infWidth M + a) ↔
      (∀ (k : ℕ) (b : Module.Basis (Fin k) ℂ M), sdpValue a (fun j => (b j : Mat ι)) = 0)) ∧
    ((∀ (k : ℕ) (b : Module.Basis (Fin k) ℂ M), sdpValue a (fun j => (b j : Mat ι)) = 0) ↔
      ∃ R ∈ omega (ι := ι) a, ∀ X ∈ M, (R * X).trace = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
