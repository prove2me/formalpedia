-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P25_normal_form_and_endpoint_signatures
-- name    : QAlgorithms.Papers.Independent.Intake100.P25.normal_form_and_endpoint_signatures
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:21:49.106886+00:00
-- url     : https://prove2.me/theorems/aa16b4f2-f7b9-4acc-a00b-4b2418846d3a
-- title:
--   Proposition 25 [Gut13]: ±1 normal form and endpoint signatures
-- statement:
--   Let $A\in\operatorname{Sp}(2n,\Omega_0)$, and let $\lambda\in\{1,-1\}$ actually be an eigenvalue. On its real generalized eigenspace $V_{[\lambda]}=\ker(A-\lambda I)^{2n}$ there is a symplectic basis giving a finite symplectic sum of blocks
--
--   $$\begin{pmatrix}J(\lambda,r_j)^{-1}&J(\lambda,r_j)^{-1}\operatorname{diag}(0,\ldots,0,d_j)\\0&J(\lambda,r_j)^\tau\end{pmatrix},\qquad d_j\in\{0,1,-1\},\quad r_j\ge1.$$
--
--   Here $J(\lambda,r)$ has diagonal $\lambda$ and upper superdiagonal $1$; $r_j$ is odd whenever $d_j=0$. The $\lambda$-eigenspace has dimension $2\#\{j:d_j=0\}+\#\{j:d_j\ne0\}$. For every $k\ge1$, the form $\widehat Q_k(v,w)=\Omega_0((A-\lambda I)^kv,(A-\lambda I)^{k-1}w)$ on $\ker(A-\lambda I)^{2k}$ is symmetric, and
--
--   $$\sum_jd_j=\lambda\sum_{k=1}^{2n}\operatorname{Sign}(\widehat Q_k).$$
--
--   Signature includes degenerate forms; the source sum has zero terms beyond this finite bound. This normal form is credited to [Gut13] and supplies the endpoint correction signs. **Source correction:** the printed eigenspace label is $1$; it is changed to $\lambda$, because $\lambda=-1$ is explicitly allowed and $A=-I$ contradicts the literal label. Independent moderation of this correction remains required.
-- source:
--   Generalized Conley-Zehnder index, arXiv:1307.7239v1, PDF p. 17, Proposition 25 [Gut13]

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P25

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Intake100.P25

open QAlgorithms.Papers.Independent.Gap50repair.P01

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

attribute [local instance] Classical.propDecidable

/-- Proposition 25 [Gut13], PDF p.17: full normal form, eigenspace count,
symmetry and the sign-sum identity. Printed: 'eigenspace of eigenvalue 1'.
Changed: eigenvalue lambda, since lambda may equal -1; the literal wording
fails for A=-I in dimension two. This correction needs independent moderation. -/
theorem normal_form_and_endpoint_signatures {n : ℕ} (A : GroupedRealMatrix n)
    (hA : IsSymplectic A) (lambda : ℤ) (hlambda : lambda = 1 ∨ lambda = -1)
    (heigen : ∃ v : Coord n → ℝ, v ≠ 0 ∧ realShift A lambda v = 0) :
    ∃ N : NormalFormData A lambda,
      Module.finrank ℝ (LinearMap.ker (realShift A lambda)) =
        2*((Finset.univ.filter (fun j => N.sign j = 0)).card) +
          (Finset.univ.filter (fun j => N.sign j ≠ 0)).card ∧
      (∀ k : ℕ, 1 ≤ k → ∀ v ∈ LinearMap.ker (realShift A lambda ^ (2*k)),
        ∀ w ∈ LinearMap.ker (realShift A lambda ^ (2*k)),
        endpointForm A lambda k v w = endpointForm A lambda k w v) ∧
      normalSignSum N = lambda * endpointSignatureSum A lambda := by sorry

end QAlgorithms.Papers.Independent.Intake100.P25

end
