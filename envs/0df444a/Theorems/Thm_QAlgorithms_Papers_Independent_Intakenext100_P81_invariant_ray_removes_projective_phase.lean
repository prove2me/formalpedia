-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P81_invariant_ray_removes_projective_phase
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P81.invariant_ray_removes_projective_phase
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:01:00.67064+00:00
-- url     : https://prove2.me/theorems/e9dbc56c-88f5-4c36-b1c3-937fbb0bc0ce
-- title:
--   An invariant vacuum ray trivializes a scalar projective multiplier
-- statement:
--   Let $G$ be a Lie group and $\mathcal H$ a complex Hilbert space. Let $U(g)$ be unitary, with circle-valued scalar multiplier $a(g,h)$ satisfying $U(g)U(h)=a(g,h)U(gh)$. Suppose that a unit vector $\Omega$ satisfies $U(g)\Omega=c(g)\Omega$, where $|c(g)|=1$. Then
--
--   $$a(g,h)=\frac{c(g)c(h)}{c(gh)},\qquad \widetilde U(g)=\overline{c(g)}U(g),\qquad \widetilde U(g)\widetilde U(h)=\widetilde U(gh).$$
--
--   The improved unitaries fix $\Omega$ and induce exactly the same conjugation on every bounded operator as the original unitaries. This removes the projective phase when an invariant ray exists. No continuity or continuous logarithm for the phases is assumed.
-- source:
--   Symmetries in quantum field theory and quantum gravity, arXiv:1810.05338v2, PDF p. 136, Appendix B: remove an unbroken projective phase

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P81

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P81

open scoped BigOperators ComplexConjugate Manifold ContDiff

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [hilbertComplete : CompleteSpace H]

section Lie

variable {m : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  [lieCharts : ChartedSpace (EuclideanSpace ℝ (Fin m)) G]
  [lieSmooth : LieGroup 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G]
  [lieHausdorff : T2Space G] [lieSecondCountable : SecondCountableTopology G]

include hilbertComplete lieCharts lieSmooth lieHausdorff lieSecondCountable

/-- Appendix B, PDF p.136 (B.1)--(B.4). Circle-valued phases avoid an unsupported
choice of continuous real logarithm. The improved operators have exactly the same conjugation. -/
theorem invariant_ray_removes_projective_phase (U : G → H ≃ₗᵢ[ℂ] H)
    (c : G → ℂ) (multiplier : G → G → ℂ) (vac : H)
    (hnorm : ‖vac‖ = 1) (hc : ∀ g, ‖c g‖ = 1)
    (hmultiplier : ∀ g h, ‖multiplier g h‖ = 1)
    (hprojective : ∀ g h v, U g (U h v) = multiplier g h • U (g * h) v)
    (hfixedRay : ∀ g, U g vac = c g • vac) :
    (∀ g h, multiplier g h = c g * c h / c (g * h)) ∧
    ∃ improved : G →* (H ≃ₗᵢ[ℂ] H),
      (∀ g v, improved g v = star (c g) • U g v) ∧
      (∀ g, improved g vac = vac) ∧
      (∀ g (O : H →L[ℂ] H), adjointConjugationCLM (improved g) O = adjointConjugationCLM (U g) O) := by sorry

end Lie

end Hilbert

end QAlgorithms.Papers.Independent.Intakenext100.P81

end
