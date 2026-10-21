-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_passive_coherent_action
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.passive_coherent_action
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:05:28.701258+00:00
-- url     : https://prove2.me/theorems/c70c731a-c1a4-406a-ba6f-97a79ea298d4
-- title:
--   §VII (7.8): passive coherent-state action
-- statement:
--   Let $n\ge1$, let $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$, and use grouped $(q_1,\ldots,q_n,p_1,\ldots,p_n)$ coordinates. Write $\mathrm{Sp}$ for the real matrices satisfying $S\beta S^T=\beta$, $K=\mathrm{Sp}\cap O(2n)$, and $\Pi$ for the symmetric positive definite matrices in $\mathrm{Sp}$. Let $H=L^2(\mathbb R^n,dq;\mathbb C)$, with $\hbar=1$, and $D(d,p)f(q)=e^{ip\cdot(q-d/2)}f(q-d)$. An implementer of $S$ is a surjective complex-linear Hilbert isometry satisfying $UD(z)=D(Sz)U$; equalities of wavefunctions mean almost-everywhere equalities. Let $U_0=X-iY\in U(n)$ and use the concrete coherent states just defined. Here $|0\rangle(q)=\pi^{-n/4}e^{-q^Tq/2}$ and $|z\rangle=D(\sqrt2\Re z,\sqrt2\Im z)|0\rangle$.
--
--   $$
--   \Gamma(U_0)|z\rangle=|U_0z\rangle\qquad\forall z\in\mathbb C^n.
--   $$
--
--   There exists a unitary implementer Gamma(U0) of K(U0) satisfying this literal equality. At z=0 it preserves the vacuum. This is the vacuum-preserving phase convention, distinct from a canonical metaplectic lift and its square-root determinant phase.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 26, §VII (7.8): passive coherent-state action

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF p.26, (7.8): exact passive coherent-state action with a chosen phase.
Printed: (7.8) omits a vacuum phase, whereas (12.6) gives the canonical
metaplectic vacuum phase c with c^2=det U.
Changed: existentially choose the vacuum-preserving unitary implementer of
this same passive matrix and retain the exact action on every coherent state.
Why: the scalar phase freedom of (2.8) permits this convention; the conclusion
at z=0 explicitly fixes vacuum preservation. The canonical metaplectic lift
and its determinant phase remain separately deferred under (12.6). -/
theorem passive_coherent_action (n : ℕ) (hn : 0 < n)
    (X Y : Matrix (Fin n) (Fin n) ℝ) (hK : IsPassive (passiveMatrix X Y)) :
    ∃ U : Schrodinger n ≃ₗᵢ[ℂ] Schrodinger n, IsImplementer (passiveMatrix X Y) U ∧
      ∃ coherent : (Fin n → ℂ) → Schrodinger n,
        (∀ z, (fun q => coherent z q) =ᵐ[volume] coherentWave z) ∧
        (∀ z, U (coherent z) = coherent (Matrix.mulVec (unitaryParameter X Y) z)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
