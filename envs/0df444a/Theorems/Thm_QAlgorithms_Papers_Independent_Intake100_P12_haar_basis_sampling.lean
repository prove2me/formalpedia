-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_haar_basis_sampling
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.haar_basis_sampling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:01:42.316643+00:00
-- url     : https://prove2.me/theorems/727d18e4-8d5a-4beb-a563-697035c2874e
-- title:
--   Haar samples span the actual moment space almost surely
-- statement:
--   Let $d,k\ge1$, let $V_{d,k}=\operatorname{span}_{\mathbb C}\{C(U^{\otimes k}):U\in U(d)\}$, and put $D=\dim_{\mathbb C}V_{d,k}$. For $D$ independent draws $U_i$ from normalized Haar measure on $U(d)$,
--
--   $$\Pr\bigl[\{C(U_i^{\otimes k})\}_{i=1}^{D}\text{ is linearly independent}\bigr]=1.$$
--
--   Independence concerns the repeated-channel Choi representatives. This is an almost-sure spanning assertion, not a finite stopping test or an efficient algorithm in $d,k$.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 7, III, unnumbered Haar sampling claim

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.7: D independent Haar samples have independent repeated-channel
Choi representatives almost surely, where D is the dimension of their actual span. -/
theorem haar_basis_sampling {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    let D := Module.finrank ℂ (unitarySpan d k)
    (MeasureTheory.Measure.pi (fun _ : Fin D => QAlgorithms.Schur.unitaryHaar d))
      {B | LinearIndependent ℂ (fun i : Fin D => repeatedChoi k (B i))} = 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
