-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P88_corner_endomorphisms
-- name    : QAlgorithms.Papers.Independent.Intake100.P88.corner_endomorphisms
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:36:49.855876+00:00
-- url     : https://prove2.me/theorems/1f3aa44a-f34a-456d-984e-fc83203d31fe
-- title:
--   Unnumbered (2.31): endomorphisms of an idempotent left ideal
-- statement:
--   Let $A$ be a unital complex algebra and let $p\ne0$ satisfy $p^2=p$. The left ideal $Ap$ consists of the elements fixed by right multiplication by $p$. Right multiplication gives a ring isomorphism
--
--   $$(pAp)^{\mathrm{op}}\xrightarrow{\ \sim\ }\operatorname{End}_A(Ap),\qquad c\longmapsto(a\longmapsto ac).$$
--
--   The corner has identity $p$. The displayed formula specifies the isomorphism, rather than asserting only an abstract equivalence. It relates idempotent corners to module endomorphisms.
-- source:
--   Partition Algebras, arXiv:math/0401314v2, PDF p. 16, Unnumbered (2.31): endomorphisms of an idempotent left ideal

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

open scoped BigOperators Matrix

open QAlgorithms.Papers.Independent.Information100.P65 (hookLength)

open QAlgorithms.Papers.Independent.Renew46.P30 (TensorIndex)

universe u v w x y

/-- Right multiplication identifies the opposite corner with endomorphisms, PDF p.16, (2.31). -/
theorem corner_endomorphisms (A : Type u) [Ring A] [Algebra ℂ A]
    (p : A) (_hp0 : p ≠ 0) (hp : IsIdempotentElem p) :
    ∃ e : hp.Cornerᵐᵒᵖ ≃+* Module.End A (principalLeftIdeal p),
      ∀ c : hp.Corner, ∀ a : principalLeftIdeal p,
        ((e (MulOpposite.op c)) a : A) = (a : A) * c.val := by sorry

end QAlgorithms.Papers.Independent.Intake100.P88

end
