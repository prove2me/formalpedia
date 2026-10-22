-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_gadDiagonalEntropies
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.gadDiagonalEntropies
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:45:46.192969+00:00
-- url     : https://prove2.me/theorems/63703810-b1f4-48d9-8356-70402fef07e2
-- title:
--   Diagonal-input generalized amplitude-damping entropies and spectrum
-- statement:
--   For physical survival $\eta\in[0,1]$, thermal excited population $\alpha\in[0,1]$, and input $\rho_p=\operatorname{diag}(1-p,p)$ with $p\in[0,1]$, retain Alice's normalized pure purification. Put $u=\alpha(1-\eta)(1-p)$ and $v=(1-\alpha)(1-\eta)p$. The joint output eigenvalues, with multiplicity, are
--
--   $$\lambda_1=u,\quad\lambda_2=v,\quad\lambda_{3,4}=\frac{1-u-v\pm\sqrt{1-2(u+v)+(v-u)^2}}2.$$
--
--   Bob's output is $\operatorname{diag}(1-q,q)$, with $q=\eta p+(1-\eta)\alpha$, and
--
--   $$S(B)=H_2(q),\qquad S(RB)=H_4(\lambda_1,\lambda_2,\lambda_3,\lambda_4),\quad H_4(\lambda)=-\sum_j\lambda_j\log_2\lambda_j.$$
--
--   Zero eigenvalues contribute zero entropy. This diagonal specialization is independent of the disputed general spectrum.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 4, Eqs.(11)–(13)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.4, Eqs.(11)–(13): actual diagonal-input GAD output entropy, joint
spectrum with multiplicities, and joint entropy; all zero eigenvalues are retained. -/
theorem gadDiagonalEntropies (eta alpha p : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    gadChannel eta alpha (diagonalInput p) = diagonalInput (eta*p+(1-eta)*alpha) ∧
    vnEntropy (gadChannel eta alpha (diagonalInput p)) = binEntropy2 (eta*p+(1-eta)*alpha) ∧
    HasSpectrum (dampingJointOutput (gadChannel eta alpha) p (Real.pi/2) 0)
      (gadDiagonalEigenvalues eta alpha p) ∧
    vnEntropy (dampingJointOutput (gadChannel eta alpha) p (Real.pi/2) 0) =
      entropy4 (gadDiagonalEigenvalues eta alpha p) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
