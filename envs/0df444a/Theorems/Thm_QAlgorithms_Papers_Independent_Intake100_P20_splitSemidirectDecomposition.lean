-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_splitSemidirectDecomposition
-- name    : QAlgorithms.Papers.Independent.Intake100.P20.splitSemidirectDecomposition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:33:02.052182+00:00
-- url     : https://prove2.me/theorems/72feacf5-0e3b-43fe-aea5-e8c79ced9b2a
-- title:
--   The explicit split-epimorphism decomposition
-- statement:
--   Let $s:A\to O$ and $e:O\to A$ be group homomorphisms with $s(e(x))=x$. Let $K=\ker s$ and let $O$ act on $K$ by $x\triangleright k=e(x)ke(x)^{-1}$. For the semidirect multiplication $(k,x)(l,y)=(k(x\triangleright l),xy)$, the maps
--
--   $$\varphi(a)=\bigl(ae(s(a))^{-1},s(a)\bigr),\qquad \varphi^{-1}(k,x)=ke(x)$$
--
--   are inverse group isomorphisms between $A$ and $K\rtimes O$. This identifies the specific isomorphism and action computed from the splitting.
-- source:
--   Group Objects and Internal Categories, arXiv:math/0212065v1, PDF p. 9, §3, Interlude

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20

namespace QAlgorithms.Papers.Independent.Intake100.P20

open CategoryTheory

open scoped TensorProduct Manifold ContDiff

universe u v w z

/-- PDF p. 9, Interlude: the explicit split-epimorphism isomorphism,
with precisely the conjugation action, forward coordinates and inverse map. -/
theorem splitSemidirectDecomposition {A : Type u} {O : Type v} [Group A] [Group O]
    (s : A →* O) (e : O →* A) (h : ∀ x, s (e x) = x) :
    ∃ q : A ≃* SemidirectProduct s.ker O (splitAction s e),
      (∀ a, q a = splitCoordinates s e h a) ∧
      (∀ a, q.symm a = splitAssembly s e a) ∧
      (∀ x (k : s.ker), ((splitAction s e x) k).val = e x * k.val * (e x)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P20
