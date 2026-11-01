-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P65_permCode_fourierRepetition
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P65.permCode_fourierRepetition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:39:04.284078+00:00
-- url     : https://prove2.me/theorems/e9fad72b-e2e0-4c2a-ad7f-be3a1c0bbeaf
-- title:
--   Extended-binomial code is Fourier repetition
-- statement:
--   Let $d\ge2$ and $M\ge1$ be integers. For a word $x\in\{0,\ldots,d-1\}^M$, let $|x|=\sum_i x_i$ and let $C_{d,M}(m)$ count words of excitation $m$. Let $|E_m\rangle$ be their normalized equal superposition, for $0\le m\le(d-1)M$. For $0\le\mu<d$, define $|\mu_{\rm perm'}\rangle=\sum_m e^{2\pi i\mu m/d}\sqrt{C_{d,M}(m)/d^M}\,|E_m\rangle$. Then
--
--   $$|\mu_{\rm perm'}\rangle=\left(\frac1{\sqrt d}\sum_{
--   u=0}^{d-1}e^{2\pi i\mu
--   u/d}|
--   u\rangle\right)^{\!\otimes M},\qquad \langle\mu_{\rm perm'}|
--   u_{\rm perm'}\rangle=\delta_{\mu
--   u}.$$
--
--   This exact identity concerns zero spacing. It is independent of the defective angular formula (C1) and supplies no unproved amplitude-damping correction claim.
-- source:
--   Performance and structure of single-mode bosonic codes, arXiv:1708.05010v3, PDF p. 27, Appendix C1 (C3)–(C9): new multi-qudit code is a repetition code in Fourier basis

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P65

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P65

open MeasureTheory Filter

open QAlgorithms.Papers.Independent.Frontier18.P14 (displacementEntry)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

open scoped ComplexConjugate Matrix Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.27--28 (C3)--(C9): exact repetition-code identity, with normalized
orthogonal codewords. No amplitude-damping correction claim is added. -/
theorem permCode_fourierRepetition (d M : ℕ) (hd : 2 ≤ d) (hM : 0 < M) :
    (∀ mu : Fin d, permCode d M mu = fourierProduct d M mu) ∧
    (∀ mu nu : Fin d,
      (∑ x : Fin M → Fin d, conj (permCode d M mu x) * permCode d M nu x) =
        if mu = nu then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P65

end
