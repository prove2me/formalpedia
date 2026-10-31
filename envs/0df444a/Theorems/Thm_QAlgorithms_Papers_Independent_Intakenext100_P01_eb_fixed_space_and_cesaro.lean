-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_eb_fixed_space_and_cesaro
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.eb_fixed_space_and_cesaro
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:15:36.010806+00:00
-- url     : https://prove2.me/theorems/838302be-2426-4540-9264-b6e2a797f58e
-- title:
--   Fixed space and Cesàro projection of an EB channel
-- statement:
--   Let $d\ge1$ and let $T:M_d(\mathbb C)\to M_d(\mathbb C)$ be an entanglement-breaking quantum channel. The averages $N^{-1}\sum_{m=1}^{N}T^m(A)$ converge for every operator $A$, defining a quantum channel $T_\infty$. There exist $k\ge1$ density matrices $\sigma_1,\ldots,\sigma_k$ with mutually orthogonal supports and a POVM $M_1,\ldots,M_k$ of spectral norm one such that
--   $$\{A:T(A)=A\}=\operatorname{span}_{\mathbb C}\{\sigma_1,\ldots,\sigma_k\},\qquad T_\infty(A)=\sum_i\operatorname{Tr}(M_iA)\sigma_i.$$
--   The range of $T_\infty$ is the full fixed-operator space, and $T\circ T_\infty=T_\infty\circ T=T_\infty^2=T_\infty$. In particular, the actual Cesàro projection is essentially classical-quantum, with the same density matrices as in the fixed-space description.
--
--   This is the fixed-point ingredient in the universal image-additivity characterization.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 9, Theorem 5.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- Theorem 5.3 and equations (14)–(19), PDF pp.9–10: the full complex fixed space and
the essentially-CQ representation of the actual Cesàro limit use the same orthogonally
supported density matrices. Convergence and projection identities exclude a default-limit reading. -/
theorem eb_fixed_space_and_cesaro {d : ℕ} (hd : 0 < d)
    (T : Superop (Fin d) (Fin d)) (hT : IsChannel T) (hEB : IsEB T) :
    (∀ A, Tendsto (fun N => cesaroAverage T N A) atTop (nhds (cesaroLimit T A))) ∧
    IsChannel (cesaroLimit T) ∧
    (∀ A, T (cesaroLimit T A) = cesaroLimit T A ∧
      cesaroLimit T (T A) = cesaroLimit T A ∧
      cesaroLimit T (cesaroLimit T A) = cesaroLimit T A) ∧
    Set.range (cesaroLimit T) = fixedOperators T ∧
    ∃ k : ℕ, 0 < k ∧ ∃ s : Fin k → Mat d, ∃ M : Fin k → Mat d,
      (∀ i, IsDensityMatrix (s i)) ∧
      (∀ i j, i ≠ j → s i * s j = 0) ∧
      fixedOperators T = (Submodule.span ℂ (Set.range s) : Set (Mat d)) ∧
      IsPOVM M ∧ (∀ i, specNorm (M i) = 1) ∧
      HasHolevoRepresentation (cesaroLimit T) M s := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
