-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P86_basedRingAntiAutomorphism_unique_factorization
-- name    : QAlgorithms.Papers.Independent.Intake100.P86.basedRingAntiAutomorphism_unique_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:28:16.464323+00:00
-- url     : https://prove2.me/theorems/76c31ea0-df82-4af9-8536-35ade48bc7ad
-- title:
--   Unique factorization of based anti-automorphisms
-- statement:
--   Let $(A,B)$ be a hypergroup over $\mathbb Z$ with canonical anti-involution $a\mapsto\overline a$, and let $f:A\to A$ be an anti-automorphism of its based ring. Thus $f$ is a unital additive bijection that reverses multiplication and permutes $B$; $f$ is not assumed involutive. There exists a unique based-ring automorphism $g:A\to A$ such that
--
--   $$
--    f(a)=\overline{g(a)}\qquad(a\in A).
--   $$
--
--   This is the unique factorization of a based anti-automorphism into the canonical hypergroup anti-involution and a based automorphism.
-- source:
--   Constructing cell data for diagram algebras, arXiv:math/0503751v3, PDF p. 11, Proposition 1.3.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P86

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P86

/-- Proposition 1.3.5, PDF pp.11–12: every based anti-automorphism
is bar composed with a unique based automorphism. No involutivity of f. -/
theorem basedRingAntiAutomorphism_unique_factorization
    {A I : Type*} [Ring A] (H : IntegralHypergroup A I)
    (f : BasedRingAntiAutomorphism H) :
    ∃! g : BasedRingAutomorphism H,
      ∀ a : A, f.equiv a = barredAutomorphism H g a := by sorry

end QAlgorithms.Papers.Independent.Intake100.P86

end
