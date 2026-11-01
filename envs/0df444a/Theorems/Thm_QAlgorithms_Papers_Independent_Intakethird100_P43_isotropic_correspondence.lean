-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P43_isotropic_correspondence
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P43.isotropic_correspondence
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:18:45.750781+00:00
-- url     : https://prove2.me/theorems/181fa533-d671-4ad1-b2ad-9a5eb8a05256
-- title:
--   Isotropic correspondence and complete-positive realization
-- statement:
--   All operators act on a finite bipartite space $\mathbb C^d\otimes\mathbb C^d$ in a fixed product basis. Write $\Gamma=T_2$ for Bob's partial transpose and $P_m=|\psi_m\rangle\langle\psi_m|$, where $|\psi_m\rangle=m^{-1/2}\sum_i|ii\rangle$. A density operator is positive semidefinite with complex trace exactly one. An admissible PPT map is complex-linear, positive and trace preserving, and $\Gamma_{\rm out}T\Gamma_{\rm in}$ is positive on every positive operator. A PPT channel is additionally completely positive; complete positivity of the transpose-conjugated map is not required. Fidelity means the overlap $\operatorname{tr}(P_m T(\rho))$.
--
--   Let $d\ge1$ and $m\ge2$. For a Hermitian operator $A$ satisfying $0\le A\le I$ and $-I\le mA^\Gamma\le I$, construct $B=(I-A)/(m^2-1)$ and
--
--   $$T_A(X)=\operatorname{tr}(XB)(I-P_m)+\operatorname{tr}(XA)P_m.$$
--
--   This construction gives a one-to-one correspondence between these operators $A$ and admissible PPT maps of the two-coefficient isotropic form. The maps are channels and obey $\operatorname{tr}(P_mT_A(\rho))=\operatorname{tr}(\rho A)$ for every density operator $\rho$. More generally, every positive complex-linear map of this isotropic form, even before imposing trace preservation, is completely positive.
--
--   This identifies the exact admissible witness operators with realizable channels.
-- source:
--   Distillability via protocols respecting the positivity of partial transpose, arXiv:quant-ph/0104095v2, PDF p. 2, Unnumbered discussion after Lemma 1, Eqs. (3)–(5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P43

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P43

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P04
  (gamma copies bellProjector negativeProjector werner)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

/-- PDF p.2, discussion after Lemma 1, (3)–(5): exact one-to-one correspondence,
with B=(I-A)/(m^2-1), and complete positivity of positive maps of isotropic form.
The fidelity is an overlap, not root fidelity. -/
theorem isotropic_correspondence (d m : ℕ) (hd : 0 < d) (hm : 2 ≤ m) :
    (∀ T : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ,
      (IsPPTMap T ∧ HasIsotropicForm T) ↔
        ∃! A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
          RainsFeasibleEffect m A ∧ isotropicPreparation m A = T) ∧
    (∀ A B : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      IsPositiveMap (isotropicRaw m A B) →
        Entanglement.IsCompletelyPositive (isotropicRaw m A B)) ∧
    (∀ A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, RainsFeasibleEffect m A →
      IsPositiveConjugatePPTChannel (isotropicPreparation m A) ∧
        ∀ rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
          IsDensityMatrix rho → effectProb (bellProjector m) (isotropicPreparation m A rho) = effectProb A rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P43

end
