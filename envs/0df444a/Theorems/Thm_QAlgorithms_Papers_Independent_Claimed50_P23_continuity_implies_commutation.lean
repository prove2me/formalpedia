-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_continuity_implies_commutation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.continuity_implies_commutation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:10:55.730071+00:00
-- url     : https://prove2.me/theorems/dad4ca84-d6e0-41f8-9a5a-457891b077f4
-- title:
--   Continuity implies the commutation identity
-- statement:
--   Let $\mathfrak g$ be a real Banach--Lie algebra, $H$ a complex Hilbert space, and $\alpha:\mathfrak g\to\operatorname{End}_{\mathbb C}(D)$ a real-linear, bracket-preserving, skew-symmetric representation on a dense complex linear subspace $D\subseteq H$. Assume strong continuity: $y\mapsto\alpha(y)v$ is continuous for every $v\in D$. Fix $x\in\mathfrak g$ for which $\alpha(x)$ is essentially skew-adjoint and its unitary group $U_x(t)=e^{t\overline{\alpha(x)}}$ preserves $D$ for every real $t$. Let $\mathfrak a\subseteq\mathfrak g$ be a closed real linear subspace invariant under $\operatorname{ad}x:y\mapsto[x,y]$. If $t\mapsto\alpha(y)U_x(t)v$ is continuous in $H$ for every $y\in\mathfrak a$ and $v\in D$, then
--
--   $$
--   U_x(1)\alpha(y)U_x(-1)v=\alpha(e^{\operatorname{ad}x}y)v
--   \qquad(y\in\mathfrak a,\ v\in D).
--   $$
--
--   This is an identity on the common domain $D$, providing the commutation law used in the integration criterion.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 4, Proposition 6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g] [CompleteSpace g]

/-- Proposition 6, PDF p.4: continuity implies the commutation identity on D.
Only the distinguished x needs essential skew-adjointness. The closed subspace
is invariant under ad x; it need not be a Lie subalgebra or a summand. -/
theorem continuity_implies_commutation
    [CompleteSpace H] [CompleteSpace g]
    (L : BanachLieBracket g) (D : Submodule ℂ H) (hDense : Dense (D : Set H))
    (alpha : g → D →ₗ[ℂ] D) (hRep : IsStrongRepresentation L D alpha)
    (x : g) (hA : EssentiallySkewAdjoint (onDomain D (D.subtype.comp (alpha x))))
    (hInvariant : InvariantDomain D (D.subtype.comp (alpha x)))
    (a : Submodule ℝ g) (haClosed : IsClosed (a : Set g))
    (haInvariant : ∀ y : a, L.bracket x (y : g) ∈ a)
    (hContinuous : ∀ (y : a) (v : D), Continuous (fun t : ℝ =>
      (alpha (y : g) (operatorOrbit D (D.subtype.comp (alpha x)) t v) : H))) :
    ∀ (y : a) (v : D),
      operatorExp D (D.subtype.comp (alpha x)) 1
        (alpha (y : g) (operatorOrbit D (D.subtype.comp (alpha x)) (-1) v) : H) =
      (alpha (adjointExp L 1 x (y : g)) v : H) := by sorry

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23

end
