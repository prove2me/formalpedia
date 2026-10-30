-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P10_mainLemma4_singletInitialization
-- name    : QAlgorithms.Papers.Independent.Extend50.P10.mainLemma4_singletInitialization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:38:48.02598+00:00
-- url     : https://prove2.me/theorems/10a89f91-0e5b-4aae-92f1-550e6998e882
-- title:
--   Singlet-product initialization in the prescribed isotypic and occupation spaces
-- statement:
--   Let $k,b\ge0$ be integers with $n=k+2b\ge1$, and set $\lambda=\mu=(k+b,b)$. On $n$ qubits define
--
--   $$
--   |\Psi_{\mathrm{init}}\rangle=|0\rangle^{\otimes k}\otimes\left(\frac{|01\rangle-|10\rangle}{\sqrt2}\right)^{\otimes b}.
--   $$
--
--   This is a unit vector in the physical $\lambda$-isotypic space and in the permutation module $M^\mu$ spanned by words containing $k+b$ zeros and $b$ ones. Thus it initializes the indicated sector without choosing a particular embedded Specht copy. The convention is that $|0\rangle$ has spin $S_z=+1/2$.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, PDF p. 9, Main Lemma 4: singlet-product initialization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10

noncomputable section

open scoped Matrix

open QAlgorithms

open QAlgorithms.Schur

open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF pp.9–10, Main Lemma 4: n=k+2b and mu=lambda=(k+b,b). The product is a
unit vector in the full physical lambda-isotypic space and in M^mu. This does
not choose one particular embedded copy of the Specht representation. -/
theorem mainLemma4_singletInitialization (k b : ℕ) (_hn : 1 ≤ k+2*b) :
    ‖singletInitialization k b‖ = 1 ∧
    act (physicalShapeProjector 2 (k+2*b) (twoRowDiagram k b)) (singletInitialization k b) =
      singletInitialization k b ∧
    singletInitialization k b ∈ occupationModule ![k+b, b] := by sorry

end QAlgorithms.Papers.Independent.Extend50.P10

end
