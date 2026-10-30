-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P29_reduced_error_implies_recovery
-- name    : QAlgorithms.Papers.Independent.Extend50.P29.reduced_error_implies_recovery
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:14:26.33325+00:00
-- url     : https://prove2.me/theorems/0015d60d-915c-4834-b9b6-054285669ec2
-- title:
--   Appendix B, Lemma 1: small reduced-state operator error implies high recovery fidelity
-- statement:
--   Let $G$ be finite, $d=|G|\ge1$, and $n\ge3$. Let $\Psi$ be a normalized invariant vector on $n+1$ regular registers. Put $A=\Psi_{01}$ and $A_0=\operatorname{Tr}_1 A$. For the polar encoder and the source's Schmidt decoder after fixed physical erasure $1$, the recovered channel has the equivalent formula
--   $$\mathcal R_A(\rho)=\left[\operatorname{Tr}_1\left(A^{1/2}\left(A_0^{-1/2}\rho^{\mathsf T}A_0^{-1/2}\otimes I\right)A^{1/2}\right)\right]^{\mathsf T}.$$
--   Write $F_{\rm worst}$ for its minimum root fidelity over normalized pure logical inputs, equivalently the worst input-state root fidelity. If $0\le\epsilon\le1$ and
--   $$\left\|\Psi_{01}-\frac{I}{d^2}\right\|_{\rm op}\le\frac{\epsilon}{3d^2},$$
--   then $E^\dagger E$ is positive definite and
--   $$F_{\rm worst}\ge1-\epsilon.$$
--   The norm condition itself excludes singularity; positive definiteness is not added as a separate hypothesis. The two transposes in the recovered formula follow the source's fixed computational basis.
-- source:
--   Error Correction of Quantum Reference Frame Information, arXiv:1709.04471v1, PDF p. 9, Appendix B, Lemma 1: small reduced-state operator error implies high recovery fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P29

noncomputable section

open MeasureTheory MeasureTheory.Measure

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P29

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt rectAct)

open QAlgorithms.Papers.Independent.Support21.P09 (groupLeftRegular)

/-- PDF pp.9--11, Lemma 1: small operator error forces a nonsingular polar
encoder and high root fidelity for the specified single-erasure decoder. -/
theorem reduced_error_implies_recovery
    {G : Type} [Group G] [Fintype G] {r : ℕ} (hr : 1 ≤ r)
    (ψ : EuclideanSpace ℂ (Fin (r + 3) → G)) (hstate : IsState ψ) (hinv : RegularInvariant ψ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hclose : specNorm (pairMarginal ψ - pairMixed G) ≤ ε / (3 * (Fintype.card G : ℝ) ^ 2)) :
    ((reshapedEncoder ψ)ᴴ * reshapedEncoder ψ).PosDef ∧
    1 - ε ≤ worstRootFidelity (pairMarginal ψ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P29

end
