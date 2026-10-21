-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_analytic_vector_weak_commutation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.analytic_vector_weak_commutation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:11:25.714782+00:00
-- url     : https://prove2.me/theorems/c1100dce-8bef-46a3-b592-92413dbb7a27
-- title:
--   Analytic-vector weak commutation
-- statement:
--   Let $\mathfrak g$ be a real Banach--Lie algebra and $H$ a complex Hilbert space. Let $D\subseteq D'\subseteq H$ be dense complex linear subspaces, and let $\alpha$ on $D$ and $\alpha'$ on $D'$ be strongly continuous, real-linear, bracket-preserving, skew-symmetric representations by complex linear endomorphisms. Assume $\alpha'(y)|_D=\alpha(y)$ for every $y\in\mathfrak g$. Fix $x\in\mathfrak g$ and suppose every $v\in D$ is analytic for $\alpha(x)$, meaning that for some radius $r=r(x,v)>0$,
--
--   $$
--   \sum_{n=0}^{\infty}\frac{r^n}{n!}\|\alpha(x)^n v\|<\infty.
--   $$
--
--   Write $U_x(t)=e^{t\overline{\alpha(x)}}$ for the corresponding unitary group. Then, with the inner product conjugate-linear in its first variable,
--
--   $$
--   \langle-U_x(1)\alpha(y)v,w\rangle
--   =\langle U_x(1)v,\alpha'(e^{\operatorname{ad}x}y)w\rangle
--   \quad(y\in\mathfrak g,\ v\in D,\ w\in D').
--   $$
--
--   This weak identity does not assume that either domain is preserved by $U_x(1)$. It is the analytic-vector input to the source's domain-extension argument.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 5, Proposition 7 ([FSSS72])

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g] [CompleteSpace g]

/-- Proposition 7 [FSSS72, Proposition 1], PDF pp.4--5: analytic-vector weak
commutation. Essential skew-adjointness follows from analyticity and is not
assumed. Neither D nor the extension domain is assumed unitary-invariant.
Mathlib's conjugate-linear-first convention preserves the displayed minus sign. -/
theorem analytic_vector_weak_commutation
    [CompleteSpace H] [CompleteSpace g]
    (L : BanachLieBracket g) (D E : Submodule ℂ H)
    (hDenseD : Dense (D : Set H)) (hDenseE : Dense (E : Set H)) (hDE : D ≤ E)
    (alpha : g → D →ₗ[ℂ] D) (beta : g → E →ₗ[ℂ] E)
    (hAlpha : IsStrongRepresentation L D alpha)
    (hBeta : IsStrongRepresentation L E beta)
    (hExtension : ∀ (y : g) (v : D),
      (beta y ⟨(v : H), hDE v.property⟩ : H) = (alpha y v : H))
    (x : g) (hAnalytic : ∀ v : D, IsAnalyticVector D (alpha x) v) :
    ∀ (y : g) (v : D) (w : E),
      inner ℂ (-operatorExp D (D.subtype.comp (alpha x)) 1 (alpha y v : H)) (w : H) =
      inner ℂ (operatorExp D (D.subtype.comp (alpha x)) 1 (v : H))
        (beta (adjointExp L 1 x y) w : H) := by sorry

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23

end
