-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P59_dissipationFunctional
-- name    : QAlgorithms.Papers.Independent.Information100.P59.dissipationFunctional
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:24:52.734946+00:00
-- url     : https://prove2.me/theorems/890e26bf-54ed-4d1a-b2dc-b85a1c2894ea
-- title:
--   Lemma 2.7: Dissipation functional with basis normalization
-- statement:
--   Let $d>0$ and let $F_1,\ldots,F_{d^2-1}$ be a real basis of the traceless Hermitian $d\times d$ operators, with $G_{jk}=\operatorname{Tr}(F_kF_j)$. For a Hermitian Hamiltonian $H$ and a Hermitian coefficient matrix $K$, let $\mathcal L$ be their Kossakowski action in this basis. The matrix $K$ is allowed to have either sign in the ambient real algebra. The trace on the full complex operator space satisfies
--
--   $$\operatorname{Tr}_{\mathrm{super}}\mathcal L=-d\operatorname{Tr}(KG).$$
--
--   Thus the trace is independent of $H$. For $G=I$ it equals $-d\operatorname{Tr}K$, while for $G=2I$ it equals $-2d\operatorname{Tr}K$. The real functional $\varphi(\mathcal L)=-\operatorname{Re}\operatorname{Tr}_{\mathrm{super}}\mathcal L/d$ is linear on the real algebra of complex-linear Hermiticity-preserving trace-annihilating maps. In orthonormal coordinates it equals $\operatorname{Tr}K$. For $K\succeq0$, it is nonnegative and vanishes exactly when $K=0$.
--
--   On the physical GKLS cone, the zero set of $\varphi$ consists exactly of the Hamiltonian generators; equivalently it is the edge, the set of generators whose negatives are also physical. This identifies the functional as total dissipation strength. The separate background identification of this edge with $\mathfrak{su}(d)$ is recorded under Lemma 2.5's provenance deferral.
-- source:
--   Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control, arXiv:2610.00046v1, PDF p. 5, Lemma 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF p.5, Lemma 2.7 and its following paragraph.
The superoperator trace and all three normalizations are conclusions. The physical
zero set is characterized both by Hamiltonian form and by membership of -L in the
physical cone, which is exactly its edge. The su(d) background identification is
recorded separately under the plan's Lemma 2.5 deferral. -/
theorem dissipationFunctional {d : ℕ} (hd : 0 < d)
    (F : Fin (d^2-1) → Operator d) (hF : IsTracelessHermitianBasis F)
    (H : Operator d) (hH : H.IsHermitian)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) (hK : K.IsHermitian) :
    superoperatorTrace (kossakowskiAction F H K) = -(d : ℂ) * (K * gramMatrix F).trace ∧
    (gramMatrix F = 1 →
      superoperatorTrace (kossakowskiAction F H K) = -(d : ℂ) * K.trace) ∧
    (gramMatrix F = 2 • (1 : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) →
      superoperatorTrace (kossakowskiAction F H K) = -2 * (d : ℂ) * K.trace) ∧
    (∀ L : Operator d → Operator d, IsLKAction L → (superoperatorTrace L).im = 0) ∧
    (∀ L M : Operator d → Operator d, IsLKAction L → IsLKAction M →
      dissipationStrength (L + M) = dissipationStrength L + dissipationStrength M ∧
      ∀ c : ℝ, dissipationStrength (c • L) = c * dissipationStrength L) ∧
    (gramMatrix F = 1 →
      dissipationStrength (kossakowskiAction F H K) = K.trace.re ∧
      (K.PosSemidef → 0 ≤ dissipationStrength (kossakowskiAction F H K) ∧
        (dissipationStrength (kossakowskiAction F H K) = 0 ↔ K = 0)) ∧
      ∀ L : Operator d → Operator d, IsPhysicalAction F L →
        0 ≤ dissipationStrength L ∧
        (dissipationStrength L = 0 ↔ IsHamiltonianAction L) ∧
        (dissipationStrength L = 0 ↔ IsPhysicalAction F (-L))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P59

end
