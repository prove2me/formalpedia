-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_productStateOrbitDistance
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.productStateOrbitDistance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:51:22.30846+00:00
-- url     : https://prove2.me/theorems/baced119-f8b1-4bca-8e32-12bcf0c619eb
-- title:
--   §IV.A: product orbit and entanglement distance
-- statement:
--   Let $n\ge1$, let $x\in\mathbb C^{2^n}$ be normalized, and let $y=z_1\otimes\cdots\otimes z_n$ with every $\|z_k\|_2=1$. The set of pure product projectors is exactly $\{Uyy^\dagger U^\dagger:U\in\mathrm{SU}(2)^{\otimes n}\}$. For every such $U$,
--   $$\operatorname{tr}(xx^\dagger Uyy^\dagger U^\dagger)=|\langle x,Uy\rangle|^2,\qquad\|xx^\dagger-Uyy^\dagger U^\dagger\|_F^2=2-2|\langle x,Uy\rangle|^2.$$
--   The transfer maximum is attained. Its maximizers are exactly the minimizers of the squared projector distance. Global phase disappears in the projectors, and the distance contains the factor two.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 27, §IV.A: product orbit and entanglement distance

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Pure product orbit and entanglement distance (167)--(169), PDF p.27.
The squared Frobenius distance is 2 minus twice the pureStateTransfer. -/
theorem productStateOrbitDistance {n : ℕ} (hn : 0 < n)
    (x : ArrayIndex (fun _ : Fin n => 2) → ℂ) (hx : ∑ i, Complex.normSq (x i) = 1)
    (z : (k : Fin n) → Fin 2 → ℂ) (hz : unitTensorFactors z) :
    let y := tensorProduct z
    pureProductProjectors (fun _ : Fin n => 2) =
      {P | ∃ U : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
        P = tensorUnitary U * rankOneMatrix y * (tensorUnitary U).conjTranspose} ∧
    (∀ U : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      Matrix.trace (rankOneMatrix x * tensorUnitary U * rankOneMatrix y * (tensorUnitary U).conjTranspose) =
        (Complex.normSq (vInner x ((tensorUnitary U).mulVec y)) : ℂ) ∧
      frobSq (rankOneMatrix x - tensorUnitary U * rankOneMatrix y * (tensorUnitary U).conjTranspose) =
        2 - 2 * pureStateTransfer x y (tensorUnitary U)) ∧
    (∃ U0 : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      ∀ U : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
        pureStateTransfer x y (tensorUnitary U) ≤ pureStateTransfer x y (tensorUnitary U0)) ∧
    (∀ U0 : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
      (∀ U : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
        frobSq (rankOneMatrix x - tensorUnitary U0 * rankOneMatrix y * (tensorUnitary U0).conjTranspose) ≤
          frobSq (rankOneMatrix x - tensorUnitary U * rankOneMatrix y * (tensorUnitary U).conjTranspose)) ↔
      ∀ U : (k : Fin n) → Matrix.specialUnitaryGroup (Fin 2) ℂ,
        pureStateTransfer x y (tensorUnitary U) ≤ pureStateTransfer x y (tensorUnitary U0)) := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
