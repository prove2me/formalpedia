-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P31_characteristic_hilbertSchmidtIsometry
-- name    : QAlgorithms.Papers.Independent.Next46.P31.characteristic_hilbertSchmidtIsometry
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:29:43.775368+00:00
-- url     : https://prove2.me/theorems/5c1d5a9d-f5ab-46c5-b3da-4e15f180b28b
-- title:
--   Proposition A.3: characteristic-function Hilbert–Schmidt isometry
-- statement:
--   Let $d\ge1$ and $H=L^2(\mathbb R^d,dx)$. For every trace-class operator $T$ on $H$, not necessarily positive or normalized, let $\varphi_T(q,p)=\operatorname{Tr}(W_{q,p}T)$ with $W_{q,p}f(x)=e^{ip\cdot(x-q/2)}f(x-q)$. The map $T\mapsto\varphi_T$ extends isometrically from trace-class operators to the full Hilbert–Schmidt class:
--
--   $$
--   \mathcal C:\mathcal T_2(H)\longrightarrow L^2\!\left(\mathbb R^{2d},(2\pi)^{-d}\,dq\,dp\right),\qquad \|\mathcal C(T)-\mathcal C(S)\|_2=\|T-S\|_{\rm HS}.
--   $$
--
--   Every trace-class $T$ belongs to that domain and has image $\varphi_T$ almost everywhere. This supplies the characteristic-function Hilbert–Schmidt isometry with the stated Fourier normalization.
-- source:
--   Decoherence rates for Galilean covariant dynamics, arXiv:0710.1344v2, PDF p. 23, Proposition A.3: characteristic-function Hilbert–Schmidt isometry

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P31

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal ComplexOrder Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Next46.P31

open QAlgorithms.PeriodicSchrodinger (Position)

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace)

/-- Clark, PDF pp.8,23, Proposition A.3. The extension/isometry is a conclusion,
not a Weyl-system assumption. Distance is exactly the HS distance on the domain;
trace-class operators are shown to belong to that domain and to have image phi. -/
theorem characteristic_hilbertSchmidtIsometry {I : Type*} {d : ℕ} (hd : 0 < d)
    (b : HilbertBasis I ℂ (EuclideanSchrodinger d)) :
    ∃ C : {T : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d) // IsHilbertSchmidt b T} → Lp ℂ 2 (characteristicMeasure d),
      (∀ T S, ‖C T - C S‖ = hsSize b (T.val - S.val)) ∧
      (∀ T : (EuclideanSchrodinger d →L[ℂ] EuclideanSchrodinger d), IsTraceClass T → ∃ hT : IsHilbertSchmidt b T,
        (C ⟨T, hT⟩ : PhasePoint d → ℂ) =ᵐ[characteristicMeasure d] schrodingerCharacteristic b T) := by sorry

end QAlgorithms.Papers.Independent.Next46.P31

end
