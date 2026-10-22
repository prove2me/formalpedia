-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_gadGeneralOutput
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.gadGeneralOutput
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:50:36.053999+00:00
-- url     : https://prove2.me/theorems/b3e348ee-b960-4d05-86d6-a059871cefd3
-- title:
--   Actual GAD general output blocks and Bob spectrum
-- statement:
--   Let $\eta,\alpha,p\in[0,1]$, $\theta\in[0,\pi]$, and use the zero-phase normalized purification of the qubit input with diagonal $(1-p,p)$ and off-diagonal $\sqrt{p(1-p)}\cos\theta$. Put $c=\cos\theta$, $s=\sin\theta$, and $r=\sqrt{\eta(1-p)p}$. In Bob-first order the actual thermal GAD joint output is
--
--   $$\rho_{BR}=\begin{pmatrix}Z&C\\ C^{\mathsf T}&W\end{pmatrix},$$
--   $$Z=\begin{pmatrix}(1-p)\alpha\eta+(1-\alpha)(1-p+p(1-\eta)c^2)&p(1-\alpha)(1-\eta)cs\\p(1-\alpha)(1-\eta)cs&p(1-\alpha)(1-\eta)s^2\end{pmatrix},$$
--   $$W=\begin{pmatrix}\alpha(1-p)(1-\eta)+p(\alpha+(1-\alpha)\eta)c^2&p(\alpha+(1-\alpha)\eta)cs\\p(\alpha+(1-\alpha)\eta)cs&p(\alpha+(1-\alpha)\eta)s^2\end{pmatrix},\quad C=\begin{pmatrix}rc&rs\\0&0\end{pmatrix}.$$
--
--   Alice's reference marginal is unchanged from AD and has spectrum $\ell_\pm(1)$, where $\ell_\pm(x)=[1\pm\sqrt{(1-2xp)^2+4x(1-p)pc^2}]/2$. Bob has diagonal $(1-q,q)$ and off-diagonal $rc$, with $q=\eta p+(1-\eta)\alpha$, and eigenvalues
--
--   $$\frac{1\pm\sqrt{(1-2q)^2+4\eta p(1-p)c^2}}2.$$
--
--   This computes the constructed channel output, without assuming a joint spectral formula.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 6, Eqs.(25)–(28),(34),(35)

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

/-- PDF p.6, Eqs.(25)–(28),(34),(35): actual GAD block output, unchanged Alice
reference marginal, and Bob's full spectrum. No use is made of printed Eq.(29). -/
theorem gadGeneralOutput (eta alpha p theta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    dampingJointOutput (gadChannel eta alpha) p theta 0 = gadBlockMatrix eta alpha p theta ∧
    traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      traceLeft (dampingJointOutput (adChannel eta) p theta 0) ∧
    HasSpectrum (traceLeft (dampingJointOutput (gadChannel eta alpha) p theta 0))
      (adEigenvalues 1 p theta) ∧
    traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0) =
      !![((1-(eta*p+(1-eta)*alpha) : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p+(1-eta)*alpha : ℝ) : ℂ)] ∧
    HasSpectrum (traceRight (dampingJointOutput (gadChannel eta alpha) p theta 0))
      (gadBobEigenvalues eta alpha p theta) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
