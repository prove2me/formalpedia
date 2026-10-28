-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_taq_cind
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.taq_cind
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:54:43.452977+00:00
-- url     : https://prove2.me/theorems/72c30922-fa70-4221-baa2-cb2ef5e184f7
-- title:
--   §5.3.2, Lemma taq_cind
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $a<b$ and arbitrary $P,Q$, let $\operatorname{TaQ}(z,Q)=\sum_{x\in z}\operatorname{sgn}(Q(x))$ count list occurrences, and let $\operatorname{Ind}_{(a,b)}(A/P)$ sum jumps over the distinct roots of $P$ in $(a,b)$. Then
--
--   $$\operatorname{TaQ}(\operatorname{roots}(P,a,b),Q)=\operatorname{Ind}_{(a,b)}\!\left(\frac{P'Q}P\right).$$
--
--   There is no endpoint nonvanishing restriction. Both sums are empty when $P=0$.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 25, §5.3.2, Lemma taq_cind

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 25, taq_cind; no endpoint nonvanishing guards. -/
theorem taq_cind {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (hab : a < b) (p q : Polynomial R) :
    taq (roots p a b) q = cind a b (p.derivative * q) p := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
