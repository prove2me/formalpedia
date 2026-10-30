-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P03_balancedVacuum
-- name    : QAlgorithms.Papers.Independent.Bridge50.P03.balancedVacuum
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:52:06.929778+00:00
-- url     : https://prove2.me/theorems/fda05952-f119-44e0-b52a-355d48a87959
-- title:
--   Balanced detector with vacuum trusted noise
-- statement:
--   Let $0\le\eta<1$ be the channel transmissivity and let $1\le\omega<\infty$ be the environment quadrature variance, with vacuum variance one. All logarithms and rates are in bits. Define the thermal entropy
--   $$h(x)=\frac{x+1}{2}\log_2\frac{x+1}{2}-\frac{x-1}{2}\log_2\frac{x-1}{2},\qquad x\ge1,$$
--   with $0\log_2 0=0$. For detector transmissivity $d\in[0,1]$ and finite trusted thermal variance $\gamma\ge1$, write
--   $$R(\eta,\omega,d,\gamma)=\frac12\log_2\frac{d\omega+(1-d)(1-\eta)\gamma}{(1-\eta)[d(1-\eta)\omega+(1-d)\gamma]}+h\!\left(\sqrt{\frac{\omega[d+(1-\eta)(1-d)\omega\gamma]}{d\omega+(1-\eta)(1-d)\gamma}}\right)-h(\omega).$$
--   At $d=0$ this expression is zero. The symbol $R$ denotes the signed expression, so a negative value is not asserted to be a positive achievable key yield.
--
--   A balanced detector with vacuum trusted noise satisfies
--   $$R(\eta,\omega,1/2,1)=B(\eta,\omega),$$
--   where
--   $$B(\eta,\omega)=\frac12\log_2\frac{\omega+1-\eta}{(1-\eta)[(1-\eta)\omega+1]}+h\!\left(\sqrt{\frac{\omega[1+(1-\eta)\omega]}{\omega+1-\eta}}\right)-h(\omega).$$
--   This specialization identifies the earlier balanced-detector comparison curve in the new family. The detector transmissivity is $1/2$; the channel transmissivity remains $\eta$.
-- source:
--   Secret key capacity of the thermal-loss channel: Improving the lower bound, arXiv:1609.02169v1, PDF p. 8, Section 4, unnumbered display

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P03

/-- arXiv:1609.02169v1, PDF p.8, Section 4: balanced beam splitter with
vacuum detector noise. Corrects the printed residual gamma to 1; the
radical is retained. This correction requires independent moderation. -/
theorem balancedVacuum (eta omega : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (homega : 1 ≤ omega) :
    signedDetectorRate eta omega (1 / 2) 1 =
      balancedVacuumCurve eta omega := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P03

end
