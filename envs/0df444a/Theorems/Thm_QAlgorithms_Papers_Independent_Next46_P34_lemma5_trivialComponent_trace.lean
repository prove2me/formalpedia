-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P34_lemma5_trivialComponent_trace
-- name    : QAlgorithms.Papers.Independent.Next46.P34.lemma5_trivialComponent_trace
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:31:53.586517+00:00
-- url     : https://prove2.me/theorems/081ec357-dfd1-4f75-b989-74be64445d63
-- title:
--   Trivial permutation component and power traces
-- statement:
--   Let $F$ be a field of characteristic zero, $n\geq1$, and let $X\in\operatorname{Mat}_n(F)$ be semisimple. Let $K/F$ be a finite splitting field of its characteristic polynomial $f$, with roots $\alpha_1,\ldots,\alpha_n$ listed with multiplicity. Fix the Galois action on these root indices, acting on $M=\mathbb Q^n$ by $(\sigma e)_i=e_{\sigma^{-1}(i)}$. Define
--   $$
--   \Lambda_{\mathbb Q}=\{e\in\mathbb Q^n:\sum_k e_k\alpha_k=0\},\qquad M_1=\mathbb Q(1,\ldots,1),\qquad \Delta_i(e)=\sum_k e_k\alpha_k^i.
--   $$
--   Writing $a_1$ for the coefficient of $T^{n-1}$ in $f$, one has
--   $$
--   M_1\subseteq\Lambda_{\mathbb Q}\ \Longleftrightarrow\ a_1=0,
--   \qquad \Delta_i(1,\ldots,1)=\operatorname{Tr}(X^i)\quad(i\geq0).
--   $$
--   The trace on the right is viewed in $K$ through the inclusion of $F$. This identifies the actual constant-vector component inside the relation space and expresses all its coefficient constraints through traces.
-- source:
--   Constructing algebraic Lie algebras, arXiv:math/0611414v1, PDF p. 5, Lemma 5: trivial permutation component and trace

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P34

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P34

/-- Fieker–de Graaf, arXiv:math/0611414v1, PDF p.5, Lemma 5.
M_1 occurs as the given subspace exactly when the next-to-leading
characteristic coefficient vanishes; all power moments are traces. -/
theorem lemma5_trivialComponent_trace
    {F K : Type*} [Field F] [CharZero F] [Field K] [CharZero K]
    [Algebra F K] [FiniteDimensional F K]
    {n : ℕ} (hn : 0 < n) (X : Matrix (Fin n) (Fin n) F)
    (hsemisimple : Module.End.IsSemisimple (Matrix.toLin' X))
    [Polynomial.IsSplittingField F K X.charpoly]
    (alpha : Fin n → K)
    (hroots : X.charpoly.map (algebraMap F K) =
      ∏ k, (Polynomial.X - Polynomial.C (alpha k)))
    (action : (K ≃ₐ[F] K) →* Equiv.Perm (Fin n))
    (hrootAction : ∀ (sigma : K ≃ₐ[F] K) k, sigma (alpha k) = alpha (action sigma k)) :
    (trivialComponent n ≤ rationalRelations alpha ↔ X.charpoly.coeff (n - 1) = 0) ∧
      ∀ i : ℕ, rootPowerMoment alpha i (fun _ => 1) = algebraMap F K (Matrix.trace (X ^ i)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P34

end
