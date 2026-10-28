-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P21_simple_has_apex
-- name    : QAlgorithms.Papers.Independent.Renew46.P21.simple_has_apex
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:25:41.217528+00:00
-- url     : https://prove2.me/theorems/5ad4a681-f36b-4ef4-8d42-ea240ecf9256
-- title:
--   Every simple semigroup module has an apex
-- statement:
--   Let $S$ be a finite semigroup and $K$ a commutative ring with identity. Let $M$ be a simple right $KS$-module: $MKS\ne0$, and $M$ has no proper nonzero $KS$-submodule. For $s\in S$ put $J(s)=S^1sS^1$, where $S^1$ denotes $S$ with an identity adjoined. For a Green $\mathcal J$-class $J$ put $I_J=\{s\in S:J\not\subseteq J(s)\}$. Then some regular $\mathcal J$-class $J$, meaning one containing an idempotent, satisfies
--
--   $$
--   \operatorname{Ann}_S(M)=I_J,\qquad
--   \operatorname{Ann}_S(M)=\{s\in S:ms=0\text{ for every }m\in M\}.
--   $$
--
--   Thus every simple module has an apex. This assigns the regular class needed to organize the classification of simple semigroup modules.
-- source:
--   On the irreducible representations of a finite semigroup, arXiv:0712.2076v2, PDF p. 3, Theorem 5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

/-- Theorem 5, p. 3: every simple right KS-module has a regular apex.
There is no regularity, identity, field, or finite-dimensionality assumption. -/
theorem simple_has_apex {K : Type u} {S : Type v} {M : Type w}
    [CommRing K] [Semigroup S] [Finite S] [AddCommGroup M] [Module K M]
    (rho : RightSemigroupAction K S M) (hsimple : SemigroupSimple rho) :
    ∃ J : JClass S, HasApex rho J := by sorry

end QAlgorithms.Papers.Independent.Renew46.P21
