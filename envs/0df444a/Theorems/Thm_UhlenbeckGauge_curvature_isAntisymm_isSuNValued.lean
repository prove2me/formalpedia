-- Prove2me | Theorems.Thm_UhlenbeckGauge_curvature_isAntisymm_isSuNValued
-- name    : UhlenbeckGauge.curvature_isAntisymm_isSuNValued
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-10T21:31:20.886849+00:00
-- url     : https://prove2.me/theorems/30ef1b1d-c29a-431a-84ec-5bf7926f78c5
-- title:
--   §3.1, p. 31 — the curvature $F_A$ of an $SU(n)$-connection is an antisymmetric $\mathfrak{su}(n)$-valued two-form
-- statement:
--   Let $A=\sum_\mu A_\mu\,dx^\mu$ be a smooth $SU(n)$-connection on the trivial bundle over $\mathbb R^4$: every coefficient $A_\mu$ is a $C^\infty$ map into $\mathfrak{su}(n)$, the traceless skew-Hermitian $n\times n$ complex matrices. Its curvature has coefficients
--   $$(F_A)_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu+[A_\mu,A_\nu],\qquad \mu,\nu\in\{0,1,2,3\}.$$
--   Then at every point $x\in\mathbb R^4$:
--
--   1. the coefficient family is antisymmetric, $(F_A)_{\nu\mu}(x)=-(F_A)_{\mu\nu}(x)$;
--   2. every coefficient lies in $\mathfrak{su}(n)$: $(F_A)_{\mu\nu}(x)^*=-(F_A)_{\mu\nu}(x)$ and $\operatorname{tr}(F_A)_{\mu\nu}(x)=0$.
--
--   In other words $F_A(x)$ is an $\mathfrak{su}(n)$-valued two-form, which is how the notes treat the curvature in Lemma 3.1.2 ("Given a Lie-algebra two-form $F_A$, here thought of as the curvature of some connection"). The lemma supplies exactly the hypotheses under which Lemma 3.1.2 applies to $F=F_A$, and is used in both halves of the energy identity for Proposition 3.1.1.
--
--   **Formalization Note** The two conclusions are the platform predicates `IsAntisymm` and `IsSuNValued` applied to `curvature A x`; smoothness and $\mathfrak{su}(n)$-valuedness of $A$ are the predicate `IsSUConnection A`.
-- source:
--   K. Uhlenbeck, Equations of Gauge Theory, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, 2012), Chapter 3, Section 3.1, p. 31 (the curvature F_A as a Lie-algebra-valued two-form in Lemma 3.1.2 and its application in the proof of Proposition 3.1.1)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

/-- The curvature of an `SU(n)`-connection is, at every point, an antisymmetric `su(n)`-valued
two-form (Uhlenbeck, *Equations of Gauge Theory*, notes by Fredrickson, §3.1, p. 31, where the
curvature `F_A` is treated as a Lie-algebra-valued two-form in Lemma 3.1.2): for every `x`,
`(F_A)_{νμ}(x) = −(F_A)_{μν}(x)`, and each `(F_A)_{μν}(x)` is skew-Hermitian with trace zero. -/
theorem curvature_isAntisymm_isSuNValued {n : ℕ} (A : Connection n) (hA : IsSUConnection A)
    (x : R4) : IsAntisymm (curvature A x) ∧ IsSuNValued (curvature A x) := by sorry

end UhlenbeckGauge
