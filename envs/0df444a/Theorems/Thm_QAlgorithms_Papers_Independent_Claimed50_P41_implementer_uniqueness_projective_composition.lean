-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_implementer_uniqueness_projective_composition
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.implementer_uniqueness_projective_composition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:55:39.633888+00:00
-- url     : https://prove2.me/theorems/20a0d298-e2d8-4ca7-9b77-8d93c459aabb
-- title:
--   §II (2.9): uniqueness and projective composition
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities.
--
--   $$
--   V(S)=cU(S),\qquad U(S^\prime)U(S)=c^\prime U(S^\prime S),\qquad |c|=|c^\prime|=1.
--   $$
--
--   The first assertion holds for any two implementers of the same matrix. The second holds for arbitrary chosen implementers of each of the three indicated matrices. The scalar phases may depend on these choices. This gives projective composition in the displayed multiplication order.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 6, §II (2.9): uniqueness and projective composition

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.6–7, (2.9): arbitrary implementers differ by a scalar phase,
and U(Sprime)U(S) implements Sprime*S up to a scalar phase. -/
theorem implementer_uniqueness_projective_composition (n : ℕ) (hn : 0 < n) :
    (∀ (S : Matrix (Phase n) (Phase n) ℝ), PreservesCanonicalForm S →
      ∀ U V : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n,
        IsImplementer S U → IsImplementer S V →
          ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ psi, V psi = c • U psi) ∧
    (∀ (Sprime S : Matrix (Phase n) (Phase n) ℝ),
      PreservesCanonicalForm Sprime → PreservesCanonicalForm S →
      ∀ Uprime U W : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n,
        IsImplementer Sprime Uprime → IsImplementer S U →
        IsImplementer (Sprime * S) W →
          ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ psi, Uprime (U psi) = c • W psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
