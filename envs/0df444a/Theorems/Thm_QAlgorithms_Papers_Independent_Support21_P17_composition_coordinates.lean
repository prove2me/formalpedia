-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P17_composition_coordinates
-- name    : QAlgorithms.Papers.Independent.Support21.P17.composition_coordinates
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T04:50:51.075634+00:00
-- url     : https://prove2.me/theorems/79b0bd2e-2bc7-4e46-9cad-374ab7769aa3
-- title:
--   Composition of RN coordinates
-- statement:
--   Let $m,n,d>0$, and let $T_1:M_m\to M_n$ and $T_2:M_n\to M_d$ be CP. Write $F_1=mJ(T_1)$ and $F_2=nJ(T_2)$ for their output-first RN coordinates. Let $\Omega=n^{-1/2}\sum_{\mu=1}^n f_\mu\otimes f_\mu$, and let $M_\Omega$ compress the two middle factors against $\Omega$ in factor order $d,n,n,m$. Then
--
--   $$F_{T_2\circ T_1}=M_\Omega(F_2\otimes F_1),\qquad [F_{T_2\circ T_1}]_{xi,yj}=\frac1n\sum_{\mu,\nu}(F_2)_{x\mu,y\nu}(F_1)_{\mu i,\nu j}.$$
--
--   The composite is $V_{m,d}^*(A\otimes F_{T_2\circ T_1})V_{m,d}$, and its full RN derivative is $I_m\otimes M_\Omega(F_2\otimes F_1)$. This is CP compression; no ambient trace-preservation claim is added.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, PDF p. 15, §5.1, unnumbered: composition of RN/Choi operators

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- Section 5.1, PDF pp.15–16: RN coordinates of composition are the Bell compression
of F2 tensor F1. The compression identity gives the composite map and its full RN derivative. -/
theorem composition_coordinates (m n d : ℕ) (hm : 0 < m) (hn : 0 < n) (hd : 0 < d)
    (T1 : Lin m n) (T2 : Lin n d)
    (hT1 : Entanglement.IsCompletelyPositive T1) (hT2 : Entanglement.IsCompletelyPositive T2) :
    scaledChoi (T2.comp T1) = bellCompression (scaledChoi T2) (scaledChoi T1) ∧
    (∀ A, T2 (T1 A) = (tracialV m d).conjTranspose *
      Matrix.kronecker A (bellCompression (scaledChoi T2) (scaledChoi T1)) * tracialV m d) ∧
    tracialDerivative (T2.comp T1) =
      Matrix.kronecker (1 : M m) (bellCompression (scaledChoi T2) (scaledChoi T1)) := by sorry

end QAlgorithms.Papers.Independent.Support21.P17

end
