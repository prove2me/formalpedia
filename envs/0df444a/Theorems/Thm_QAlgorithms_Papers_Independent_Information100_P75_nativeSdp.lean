-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P75_nativeSdp
-- name    : QAlgorithms.Papers.Independent.Information100.P75.nativeSdp
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:16:23.954128+00:00
-- url     : https://prove2.me/theorems/0edc4f7e-25a0-4195-9639-a1dc2b485df3
-- title:
--   Native SDP has the same attained minimum as Program 3.1
-- statement:
--   For $0\le\alpha<\pi$, the relaxed-state set consists of the matrices $\Omega_n(\alpha)=\{e^{i\alpha/2}P+e^{-i\alpha/2}Q:P,Q\succeq0,\ \operatorname{Tr}(P)+\operatorname{Tr}(Q)=1\}$. Here $P,Q$ are square complex matrices of the indicated dimension; these phase-weighted sums need not be density matrices.
--
--   Let $n\ge1$, $0\le\alpha<\pi$, and let $(A_l)_{l=1}^k$ be any basis of a complex subspace of $M_n(\mathbb C)$, allowing $k=0$. For every matrix $\rho$ and real $c_l$, the epigraph constraints satisfy
--
--   $$\begin{pmatrix}c_l&\operatorname{Tr}(\rho A_l)\\overline{\operatorname{Tr}(\rho A_l)}&c_l\end{pmatrix}\succeq0
--   \iff c_l\ge|\operatorname{Tr}(\rho A_l)|.$$
--
--   Consequently the minimum of $\sum_l c_l$ subject to these blocks, $\rho=e^{i\alpha/2}P+e^{-i\alpha/2}Q$, $P,Q\succeq0$ and $\operatorname{Tr}P+\operatorname{Tr}Q=1$ equals
--
--   $$D_\alpha(A_1,\ldots,A_k)=\min_{\rho\in\Omega_n(\alpha)}\sum_l|\operatorname{Tr}(\rho A_l)|.$$
--
--   Both minima are attained. This gives the explicit semidefinite reformulation, including the empty-basis case.
-- source:
--   Parallel quantum channel discrimination and numerical ranges in tensor product subspaces, arXiv:2609.20781v1, PDF p. 6, Appendix A, (A.1)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P75

open Classical

open scoped ComplexConjugate ComplexOrder Matrix

open MeasureTheory

/-- Appendix A, PDF p.6, (A.1), and Program (3.1) p.3: epigraph equivalence and equality
of attained minima, including the empty basis. The lower-left block is conjugated. -/
theorem nativeSdp {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Submodule ℂ (Mat ι)) {k : ℕ} (b : Module.Basis (Fin k) ℂ M)
    (a : ℝ) (ha : 0 ≤ a) (hap : a < Real.pi) :
    let X := fun j => (b j : Mat ι)
    (∀ (R : Mat ι) (c : Fin k → ℝ),
      (∀ j, (epigraphBlock (c j) ((R * X j).trace)).PosSemidef) ↔
      (∀ j, ‖(R * X j).trace‖ ≤ c j)) ∧
    nativeValue a X = sdpValue a X ∧
    (∃ R ∈ omega (ι := ι) a, traceModulusObjective X R = sdpValue a X ∧
      ∀ S ∈ omega (ι := ι) a, traceModulusObjective X R ≤ traceModulusObjective X S) ∧
    (∃ P Q c, NativeFeasible a X P Q c ∧ (∑ j, c j) = sdpValue a X ∧
      ∀ P2 Q2 c2, NativeFeasible a X P2 Q2 c2 → (∑ j, c j) ≤ ∑ j, c2 j) := by sorry

end QAlgorithms.Papers.Independent.Information100.P75

end
