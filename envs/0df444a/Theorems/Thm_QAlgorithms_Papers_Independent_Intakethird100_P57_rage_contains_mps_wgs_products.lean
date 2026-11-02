-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_rage_contains_mps_wgs_products
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.rage_contains_mps_wgs_products
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:08:03.945434+00:00
-- url     : https://prove2.me/theorems/e3f763b3-cfb8-4fcb-b584-6f1f774a263c
-- title:
--   Unnumbered main construction: RAGE contains MPS and weighted-graph/product-superposition states
-- statement:
--   Let $N,D\ge1$. For site matrices $A_{k,b}\in\mathbb C^{D\times D}$, let $M(A)$ have amplitudes $\operatorname{tr}(A_{1,b_1}\cdots A_{N,b_N})$. Let $W_\Phi$ apply $\operatorname{diag}(1,1,1,e^{i\Phi_{jk}})$ once per unordered pair, where $\Phi$ is symmetric, has zero diagonal, and has entries in $[0,2\pi)$. Let $V=\bigotimes_k V_k$, $V_k\in U(2)$, and set $R(A,\Phi,V)=VW_\Phi M(A)$. Then
--
--   $$R(A,0,I)=M(A),\qquad R(A(r),\Phi,V)=VW_\Phi\bigotimes_k|+\rangle.$$
--
--   Here the second equality uses bond-one tensors with both local amplitudes $1/\sqrt2$. More generally, for $m\ge1$, arbitrary coefficients $c_t$, and arbitrary product factors $r_{t,k}(b)$, the diagonal tensors $B_{k,b}(t,t)=r_{t,k}(b)$, with an additional factor $c_t$ at the first site, satisfy
--
--   $$R(B,\Phi,V)=VW_\Phi\sum_{t=1}^m c_t\bigotimes_k r_{t,k}.$$
--
--   These are exact raw-vector containments, with one common graph and rotation family. Physical states are obtained by normalizing nonzero vectors. In Eq.(3), the factors $\eta(d)$ have amplitudes $(1,e^d)$; the conflicting first-line exponent is not asserted.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 1, Unnumbered main construction: RAGE contains MPS and weighted-graph/product-superposition states

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF pp.1–2, Eqs.(1)–(3): exact raw-vector containments, including finite
superpositions under one common graph and common rotations. Only the unambiguous second
line of Eq.(3) is used; its conflicting first-line quadratic exponent is deferred. -/
theorem rage_contains_mps_wgs_products {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ) :
    rage A (emptyPhaseGraph N) (fun _ => 1) = traceMPS A ∧
    rage (productTensors (plusFactors N)) G V =
      enhance G V (productVec (plusFactors N)) ∧
    (∀ (m : ℕ), 1 ≤ m → ∀ (c : Fin m → ℂ)
      (r : Fin m → Fin N → Bool → ℂ),
      rage (diagonalTensors c r) G V = enhance G V (∑ t, c t • productVec (r t))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
