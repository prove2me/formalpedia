-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P28_unital_optimum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P28.unital_optimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:22:20.577212+00:00
-- url     : https://prove2.me/theorems/714ccbd0-5652-4918-b344-4c0d42387917
-- title:
--   Optimal unital tomography with a singular full frame
-- statement:
--   For common dimension $d\ge1$, prior mean Choi matrix $I/d$, and identity representation, every physical tester and finite-loss unbiased dual reconstructing the complex unital-channel span satisfies
--
--   $$\eta_{\mathcal U}\ge(d^2-1)^3+1.$$
--
--   Equality is attained by the Haar orbit of $\Pi_0=d|\Psi\rangle\!\rangle\langle\!\langle\Psi|$ with $\Psi=I/\sqrt d$ (equivalently $\beta=0$). The setup uses a distinct normalized maximally entangled channel input and measurement density $d\Pi$. Its frame is complete on the unital span and has an attaining unbiased dual. For $d\ge2$ it has $A=B=0$, so completeness is not imposed on the full operator space. At $d=1$ the minimum is $1$. The support inverse, rather than an invalid full inverse, expresses the optimum.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, PDF p. 3, (34), third line; (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.3, (34) third line, and p.4: global unital-channel minimum, attained at beta=A=0.
Completeness is on the unital span; full informational completeness is not required. -/
theorem unital_optimum {d : ℕ} (hd : 0 < d)
    (haar : Measure (SU d)) (hhaar : IsProbabilityHaar haar) :
    (∀ (X : Type) [MeasurableSpace X] (mu : Measure X) [SFinite mu]
      (P D : X → Op (ChoiBasis d)), TomographyAdmissible mu P D .unital →
      ((d : ℝ)^2 - 1)^3 + 1 ≤ eta .unital mu P D) ∧
    (∀ psi : EuclideanSpace ℂ (Fin d), QAlgorithms.IsState psi → Attains haar .unital psi) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P28

end
