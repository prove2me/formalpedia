-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P23_automatic_extension_representation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P23.automatic_extension_representation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:11:58.565479+00:00
-- url     : https://prove2.me/theorems/b5ea5860-24b6-4408-8dc9-81d2087eed71
-- title:
--   Automatic representation on a common extension domain
-- statement:
--   Let $\mathfrak g$ be a real Banach--Lie algebra and $\alpha:\mathfrak g\to\operatorname{End}_{\mathbb C}(D)$ a strongly continuous, real-linear, bracket-preserving, skew-symmetric representation on a dense complex linear subspace $D$ of a complex Hilbert space $H$. Let $D'\subseteq H$ be a complex linear subspace containing $D$. Suppose that for each $y\in\mathfrak g$ one is given a complex linear skew-symmetric endomorphism $\alpha'(y):D'\to D'$ restricting to $\alpha(y)$ on $D$. Then
--
--   $$
--   \alpha':\mathfrak g\longrightarrow\operatorname{End}_{\mathbb C}(D')
--   \quad\text{is a strongly continuous real Lie algebra representation.}
--   $$
--
--   In particular, real linearity, bracket preservation, and continuity of $y\mapsto\alpha'(y)w$ for every $w\in D'$ are conclusions. This allows constructing the extended representation from its individual skew-symmetric operators.
-- source:
--   Integrating representations of Banach--Lie algebras, arXiv:1003.0999v3, PDF p. 5, Unnumbered remark after Proposition 7

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P23

noncomputable section

open MeasureTheory

open scoped Interval Classical

namespace QAlgorithms.Papers.Independent.Claimed50.P23

section HilbertStatements

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {g : Type*} [NormedAddCommGroup g] [NormedSpace ℝ g] [CompleteSpace g]

/-- Unnumbered remark after Proposition 7, PDF p.5: a skew-symmetric family of
extensions on a common invariant domain is automatically a strongly continuous
real-linear Lie algebra representation. These conclusions are not hypotheses. -/
theorem automatic_extension_representation
    [CompleteSpace H] [CompleteSpace g]
    (L : BanachLieBracket g) (D E : Submodule ℂ H)
    (hDense : Dense (D : Set H)) (hDE : D ≤ E)
    (alpha : g → D →ₗ[ℂ] D) (hAlpha : IsStrongRepresentation L D alpha)
    (beta : g → E →ₗ[ℂ] E)
    (hSkew : ∀ (y : g) (v w : E),
      inner ℂ (beta y v : H) (w : H) = -inner ℂ (v : H) (beta y w : H))
    (hExtension : ∀ (y : g) (v : D),
      (beta y ⟨(v : H), hDE v.property⟩ : H) = (alpha y v : H)) :
    IsStrongRepresentation L E beta := by sorry

end HilbertStatements

end QAlgorithms.Papers.Independent.Claimed50.P23

end
