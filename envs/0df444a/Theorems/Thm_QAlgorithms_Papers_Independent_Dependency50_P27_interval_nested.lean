-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_interval_nested
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.interval_nested
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:44:12.598203+00:00
-- url     : https://prove2.me/theorems/ba9d2a82-d922-4b65-8e6b-648d84a578c4
-- title:
--   §3.3, unnumbered interval nesting
-- statement:
--   Let $R$ be a discrete totally ordered integral domain, with order compatible with its ring operations. For $a,b,c,d,x\in R$, using closed intervals,
--
--   $$c,d\in[a,b],\quad x\in[c,d]\quad\Longrightarrow\quad x\in[a,b].$$
--
--   This packages the endpoint inequalities without additional ordering assumptions.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 13, §3.3, unnumbered interval nesting

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 13–14, the displayed closed-interval nesting statement. -/
theorem interval_nested {R : Type*} [CommRing R] [IsDomain R]
    [LinearOrder R] [IsStrictOrderedRing R] (a b c d x : R)
    (hc : c ∈ Set.Icc a b) (hd : d ∈ Set.Icc a b) (hx : x ∈ Set.Icc c d) :
    x ∈ Set.Icc a b := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
