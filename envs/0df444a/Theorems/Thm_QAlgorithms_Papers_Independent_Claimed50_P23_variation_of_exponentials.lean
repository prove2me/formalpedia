-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_variation_of_exponentials
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.variation_of_exponentials
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:12:28.875297+00:00
-- url     : https://prove2.me/theorems/3e789d17-7c66-4301-99bb-3e83a2ba5f5a
-- title:
--   Variation-of-exponentials integral identity
-- statement:
--   Let $H$ be a complex Hilbert space and $A,B:D\to H$ complex linear essentially skew-adjoint operators on the same dense complex linear domain $D$. Put $U_A(s)=e^{s\overline A}$ and $U_B(s)=e^{s\overline B}$. Suppose $U_A(s)D\subseteq D$ for every real $s$. If $v\in D$ and $s\mapsto BU_A(s)v$ is continuous, then for every $t\in\mathbb R$ the integrand below is Bochner integrable on the interval between $0$ and $t$, and
--
--   $$
--   U_B(t)v-U_A(t)v=\int_0^t U_B(s)(B-A)U_A(t-s)v\,ds.
--   $$
--
--   The integral is oriented when $t<0$. Neither $A$ nor $B$ is required to map $D$ into $D$, and invariance under $U_B$ is not assumed. The identity compares flows of different unbounded generators.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 6, Lemma 9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 9, PDF p.6: the oriented variation-of-exponentials identity. Neither
operator is required to map D into D, and no invariance under B is assumed.
Integrability is part of the conclusion, preventing a default-zero integral. -/
theorem variation_of_exponentials
    [CompleteSpace H]
    (D : Submodule ℂ H) (hDense : Dense (D : Set H))
    (A B : D →ₗ[ℂ] H)
    (hA : EssentiallySkewAdjoint (onDomain D A))
    (hB : EssentiallySkewAdjoint (onDomain D B))
    (hInvariant : InvariantDomain D A) (v : D)
    (hContinuous : Continuous (fun s : ℝ => B (operatorOrbit D A s v))) :
    ∀ t : ℝ,
      IntervalIntegrable (fun s : ℝ => operatorExp D B s
        (B (operatorOrbit D A (t - s) v) - A (operatorOrbit D A (t - s) v))) volume 0 t ∧
      operatorExp D B t (v : H) - operatorExp D A t (v : H) =
        ∫ s in (0 : ℝ)..t, operatorExp D B s
          (B (operatorOrbit D A (t - s) v) - A (operatorOrbit D A (t - s) v)) := by sorry

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23

end
