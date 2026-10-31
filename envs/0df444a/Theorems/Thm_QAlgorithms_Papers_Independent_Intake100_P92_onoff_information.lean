-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P92_onoff_information
-- name    : QAlgorithms.Papers.Independent.Intake100.P92.onoff_information
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:38:01.612904+00:00
-- url     : https://prove2.me/theorems/c9a7d136-69fa-43b3-ae0d-59a79580ee08
-- title:
--   Ideal on/off Z-channel information and optimal nonempty fraction
-- statement:
--   Let independent on/off inputs have nonempty probability $q\in[0,1]$, with no Eve or dark counts. For a nonempty pulse the receiver clicks with probability $x\in[0,1]$; an empty pulse never clicks. Let $I(q,x)$ be the mutual information of this actual Z-channel joint law, and let $h$ be binary entropy in bits. Then
--
--   $$I(q,x)=h(qx)-qh(x),\qquad \lim_{x\downarrow0}\frac{I(q,x)}x=-q\log_2q\le\frac1{e\ln2}.$$
--
--   The continuous coefficient is zero at $q=0,1$ and attains its maximum at $q=e^{-1}$. With $\mu>0$ and $0<\eta\le1$, substituting the exact coherent click probability $x=1-e^{-\mu t\eta}$ gives the same coefficient for $I/(\mu t\eta)$ as $t\downarrow0$. The source’s displayed $h(q\mu t\eta)-qh(\mu t\eta)$ uses its first-order detector channel. The raw symbol rate is one, so this is the leading ideal information rate per slot. No security result for the variant is asserted.
-- source:
--   Upper Bounds for the Security of two Distributed-Phase Reference Protocols of Quantum Cryptography (Coherent-One-Way and Differential-Phase-Shift), arXiv:0710.4884v2, PDF p. 11, Appendix A, unnumbered: on/off Z-channel ideal information and optimal pulse fraction

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P92

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Intake100.P92

open QAlgorithms.Papers.Independent.Information100.P21 (Vec tensor)

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

open QAlgorithms.Papers.Independent.Frontier18.P14
  (Fock coherentPair coherentPairCoefficients passiveApply passiveCoefficients
   fockReducedFirst reducedSecond coherentCoefficient)

/-- Appendix A p.11: entropy formula for the linearized Z-channel, its leading
coefficient, and the optimal nonempty-pulse fraction. The exact coherent-detector
channel instead substitutes x=1-exp(-mu t eta), with the same leading coefficient. -/
theorem onoff_information (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    (∀ x ∈ Set.Icc (0:ℝ) 1, zInfo q x =
      QAlgorithms.binEntropy2 (q*x)-q*QAlgorithms.binEntropy2 x) ∧
    Tendsto (fun x => zInfo q x / x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (zCoefficient q)) ∧
    zCoefficient q ≤ 1/(Real.exp 1 * Real.log 2) ∧
    zCoefficient (Real.exp (-1)) = 1/(Real.exp 1 * Real.log 2) ∧
    (∀ (mu eta : ℝ), 0 < mu → 0 < eta → eta ≤ 1 →
      Tendsto (fun t => zInfo q (click mu t eta)/(mu*t*eta))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (zCoefficient q))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P92

end
