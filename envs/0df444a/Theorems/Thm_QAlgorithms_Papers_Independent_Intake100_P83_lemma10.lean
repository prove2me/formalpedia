-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P83_lemma10
-- name    : QAlgorithms.Papers.Independent.Intake100.P83.lemma10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:25:20.523654+00:00
-- url     : https://prove2.me/theorems/f0450fb8-e8af-4b4d-ad87-0b773487ba05
-- title:
--   Lemma 10: lifting an embedded partial swap to a full two-level rotation
-- statement:
--   Let $A$ be a finite nonempty orthonormal on-site basis. Choose $c\le n$ distinct named sites, represented by an injection $f:\{1,\ldots,c\}\hookrightarrow\{1,\ldots,n\}$. Let $t,u\in A^c$ and let $r\ne s\in A^n$ satisfy the exact transition
--
--   $$
--   |s\rangle=\bigl(X_f(t;u)\otimes I_{\overline{f}}\bigr)|r\rangle,
--   \qquad X(t;u)=|t\rangle\langle u|+|u\rangle\langle t|.
--   $$
--
--   Then every $e^{i\theta X(r;s)}$, $0\le\theta<2\pi$, is an exact finite product of the supplied family $e^{i\phi X_f(t;u)}\otimes I_{\overline f}$, $0\le\phi<2\pi$, and the two-site phases $I-2|ab\rangle\langle ab|$ on arbitrary site pairs. No symmetry hypothesis is needed.
--
--   The supplied operator is a partial swap, not an arbitrary full swap. This lifts a local transition while selecting the complete external basis context.
-- source:
--   Theory of Quantum Circuits with Abelian Symmetries, arXiv:2302.12466v3, PDF p. 14, Lemma 10: lift a local transition to a full two-level transition

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P83

noncomputable section

open scoped BigOperators ComplexConjugate Matrix Kronecker Manifold ContDiff

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

namespace QAlgorithms.Papers.Independent.Intake100.P83

variable {A G : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.14 Lemma 10: lift the supplied embedded partial-swap transition, with identity
on the complement, to a full-system two-level rotation using only that continuous family
and the controlled phases Eq.(37). No symmetry assumption is needed. -/
theorem lemma10 [Nonempty A] (n c : ℕ) (hcn : c ≤ n) (f : Fin c ↪ Fin n)
    (r s : Words A n) (hrs : r ≠ s) (t u : Words A c)
    (htransition : QAlgorithms.act (embedOnSites f (twoX t u)) (QAlgorithms.ket r) = QAlgorithms.ket s) :
    ∀ theta ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      positiveImaginaryEvolution (twoX r s) theta ∈ finiteGateProducts (czFamily A n ∪
        {B | ∃ phi ∈ Set.Ico (0 : ℝ) (2 * Real.pi), B = embedOnSites f (positiveImaginaryEvolution (twoX t u) phi)}) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P83

end
