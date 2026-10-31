-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P86_subdatum_inherits_tabularity_and_trace
-- name    : QAlgorithms.Papers.Independent.Intake100.P86.subdatum_inherits_tabularity_and_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:29:00.094177+00:00
-- url     : https://prove2.me/theorems/777d53f2-99a9-4184-913f-945e8fe5e65d
-- title:
--   Subdata inherit tabularity and tabularity with trace
-- statement:
--   Put $L=\mathbb Z[v,v^{-1}]$. Let $A$ be a tabular $L$-algebra with table datum $D=(\Lambda,\Gamma,B,M,C,*)$ and distinguished mutually orthogonal idempotents $\{1_\epsilon:\epsilon\in E\}$ from axiom A1. Let $A'\subseteq A$ be an $L$-subalgebra, and let $D'=(\Lambda',\Gamma',B',M',C',*')$ be a subdatum in the sense of S1–S3: the label poset, half-index sets, and unital based hypergroups embed into those of $D$; $C'$ and $*'$ are restrictions; and the displayed restricted basis spans $A'$. Assume $1_\epsilon\in A'$ for every $\epsilon\in E$. Then
--
--   $$
--    D'\text{ is a table datum for }A',\qquad
--    (A,D)\text{ tabular with trace}\ \Longrightarrow\ (A',D')\text{ tabular with trace}.
--   $$
--
--   The first assertion includes all of A1–A3 for the given tuple, with multiplication modulo strictly lower layers and coefficients independent of the right half-index and the middle argument. The second includes A4–A5, with the source's normalization: for $X=C^b_{S,T}$, the trace satisfies $\tau(v^{a(X)}X)\equiv1$ if $S=T$ and $b=1$, and is congruent to zero otherwise, modulo $v^{-1}\mathbb Z[v^{-1}]$. Here $a(X)$ is the maximum Laurent degree among structure coefficients whose output is $X$.
--
--   The proposition transfers the prescribed table structure, and its trace refinement when available, to the specified subalgebra.
--
--   **Formalization Note** Middle coefficients in $L\otimes_{\mathbb Z}\Gamma(\lambda)$ are represented by finitely supported $L$-valued coordinates in its free hypergroup basis. The degree maximum is encoded by its universal upper bound and attainment, avoiding any default value for an unbounded supremum.
-- source:
--   Constructing cell data for diagram algebras, arXiv:math/0503751v3, PDF p. 14, Proposition 2.1.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P86

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P86

universe u

/-- Proposition 2.1.5, PDF pp.14–15: the specified subdatum inherits
A1–A3 when it contains every distinguished idempotent. If the ambient datum
also has A4–A5, then the restriction has A4–A5, with the printed trace
normalization. The conclusion concerns the given tuple. -/
theorem subdatum_inherits_tabularity_and_trace
    {A E : Type u} [Ring A] [Algebra TabularScalars A]
    (D : TableCandidate A) (e : E → A) (hD : IsTableDatum D e)
    (A2 : Subalgebra TabularScalars A) (D2 : TableCandidate A2)
    (sub : TableSubdatum D A2 D2) (he : ∀ i, e i ∈ A2) :
    IsTableDatum D2 (fun i => (⟨e i, he i⟩ : A2)) ∧
      (HasTabularTrace D → HasTabularTrace D2) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P86

end
