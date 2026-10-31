-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_small_dimensional_polytopic_images
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.small_dimensional_polytopic_images
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:20:39.048386+00:00
-- url     : https://prove2.me/theorems/35f1a1e1-6b0a-4e0d-bb6a-6f76d0f07dfa
-- title:
--   Polytopic channel images in small affine dimensions
-- statement:
--   Consider quantum channels between positive finite matrix dimensions, and measure physical-image dimension as real affine dimension. Every such channel $T$ with polytopic image of dimension $0$ or $1$ is classical-quantum and hence entanglement breaking. For each $r\in\{2,3\}$ there exist positive dimensions and a quantum channel $T$ such that
--   $$\dim_{\mathrm{aff},\mathbb R}\operatorname{Im}T=r,\quad\operatorname{Im}T\text{ is polytopic},\quad T\text{ is entanglement breaking},\quad T\text{ is not essentially classical-quantum}.$$
--
--   The low-dimensional universal statement is distinct from the existential statements in dimensions two and three.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 15, Proposition 7.5

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

/-- Proposition 7.5, PDF p.15: universal CQ/EB conclusion in affine dimensions 0,1;
separate existential EB but nonessential-CQ examples for each of dimensions 2,3. -/
theorem small_dimensional_polytopic_images :
    (∀ d n : ℕ, 0 < d → 0 < n → ∀ T : Superop (Fin d) (Fin n),
      IsChannel T → IsPolytopic (channelImage T) →
      (affineDimension (channelImage T) = 0 ∨ affineDimension (channelImage T) = 1) →
      HasCQRepresentation T ∧ IsEB T) ∧
    (∀ r : ℕ, (r = 2 ∨ r = 3) → ∃ d n : ℕ, 0 < d ∧ 0 < n ∧
      ∃ T : Superop (Fin d) (Fin n), IsChannel T ∧ IsPolytopic (channelImage T) ∧
        affineDimension (channelImage T) = r ∧ IsEB T ∧ ¬ IsEssentialCQ T) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
