-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_binomial_diagonalQec
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.binomial_diagonalQec
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:30:57.901365+00:00
-- url     : https://prove2.me/theorems/079928a7-c737-47e1-a325-fb8505521692
-- title:
--   Binomial identity and distortion coefficients
-- statement:
--   Let $N,S,\ell\ge0$ be integers, $0<\gamma<1$, and use the positive and negative combinations $|\pm\rangle=(|0_{\rm bin}\rangle\pm|1_{\rm bin}\rangle)/\sqrt2$ as the logical basis. For the actual compression of $E_\ell^\dagger E_\ell$, let $c_{\ell\ell}$ and $z_{\ell\ell}$ denote its identity and Z coefficients in that basis. Define $G_\pm(x)=((1\pm x^{S+1})/2)^{N+1}$. Then
--
--   $$c_{\ell\ell}=\frac{\gamma^\ell}{\ell!}G_+^{(\ell)}(1-\gamma),\qquad z_{\ell\ell}=\frac{\gamma^\ell}{\ell!}G_-^{(\ell)}(1-\gamma).$$
--
--   Polynomial derivatives make the zero above the finite support exact. No claim is made that these two coefficients alone describe the full block for every positive loss count.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 12, §VI A (6.4)–(6.5): binomial diagonal QEC coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.12 (6.4)--(6.5): only c and z are prescribed, in the plus/minus basis;
this does not erase possible other coefficients for positive loss count. -/
theorem binomial_diagonalQec (N S l : ℕ) (g : ℝ) (hg0 : 0 < g) (hg1 : g < 1) :
    qecC (binomialParity N S) g l l =
      g ^ l / Nat.factorial l *
        (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[l])
          (binomialGenerator N S false)).eval (1 - g) ∧
    qecZ (binomialParity N S) g l l =
      g ^ l / Nat.factorial l *
        (((Polynomial.derivative : Polynomial ℝ → Polynomial ℝ)^[l])
          (binomialGenerator N S true)).eval (1 - g) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
