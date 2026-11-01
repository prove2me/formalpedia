-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_return_williamson
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.return_williamson
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:20:42.073104+00:00
-- url     : https://prove2.me/theorems/1e69808f-1d77-4627-a47f-9bbe285a837a
-- title:
--   Eqs.(15)–(17): explicit symplectic diagonalization of the returned covariances
-- statement:
--   Let $N_S,N_B\ge0$ and $0<\kappa<1$. Write $S=2N_S+1$, $C_q=2\sqrt{N_S(N_S+1)}$, $B=2N_B+1$, $A=2\kappa N_S+B$, and
--   $$
--   \Delta=\sqrt{(A+S)^2-4\kappa C_q^2},\quad
--   x_\pm=\sqrt{\frac{A+S\pm\Delta}{2\Delta}},\quad
--   T=\begin{pmatrix}X_+&X_-\\X_-&X_+\end{pmatrix},\quad X_+=\operatorname{diag}(x_+,x_+),\ X_-=\operatorname{diag}(x_-,-x_-).
--   $$
--   Then $\Delta>0$, the identity diagonalizes the target-absent covariance with spectrum $(B/4,S/4)$, and $T$ is symplectic and diagonalizes the target-present covariance with
--   $$
--   \nu_k=\frac{(-1)^k(S-A)+\Delta}{8},\quad k=1,2,\qquad
--   \Lambda_{RI}^{(1)}=T\operatorname{diag}(\nu_1,\nu_1,\nu_2,\nu_2)T^T.
--   $$
--   All symplectic eigenvalues are at least $1/4$. Symplectic means $T\Omega T^T=\Omega$ for $\Omega=\bigoplus_{j=1}^2\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$. This supplies the explicit physical diagonalizations used to evaluate Gaussian overlaps.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 3, Eqs.(15)–(17): explicit symplectic diagonalization of the returned covariances

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.3, Eqs.(15)–(17), with the definition (9)–(10).
Source spectrum indices 1,2 become Fin 2 values 0,1. Delta>0 is a
conclusion, so all square-root denominators are meaningful. -/
theorem return_williamson (k NS NB : ℝ) (hk : 0 < k) (hk1 : k < 1)
    (hNS : 0 ≤ NS) (hNB : 0 ≤ NB) :
    0 < returnDiscriminant k NS NB ∧
    (∀ present : Bool, ∀ r : Fin 2, 1 / 4 ≤ returnSpectrum present k NS NB r) ∧
    G.Symplectic (1 : Cov 2) ∧
    returnCov false k NS NB = G.repeatedDiagonal (returnSpectrum false k NS NB) ∧
    G.Symplectic (williamsonT k NS NB) ∧
    returnCov true k NS NB = williamsonT k NS NB *
      G.repeatedDiagonal (returnSpectrum true k NS NB) * (williamsonT k NS NB).transpose := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
