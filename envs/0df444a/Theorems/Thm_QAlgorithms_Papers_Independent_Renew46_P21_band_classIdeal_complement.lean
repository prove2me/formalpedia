-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P21_band_classIdeal_complement
-- name    : QAlgorithms.Papers.Independent.Renew46.P21.band_classIdeal_complement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:26:20.938463+00:00
-- url     : https://prove2.me/theorems/08a8ad0f-938a-4aa8-85ab-c1c589021761
-- title:
--   The complement of I_J is a subsemigroup of a band
-- statement:
--   Let $S$ be a semigroup with $s^2=s$ for every $s\in S$, and let $J$ be a Green $\mathcal J$-class. Write $J(s)=S^1sS^1$ and $I_J=\{s\in S:J\not\subseteq J(s)\}$. Then
--
--   $$
--   S\setminus I_J\text{ is a subsemigroup of }S.
--   $$
--
--   Equivalently, if $J\subseteq J(s)$ and $J\subseteq J(t)$, then $J\subseteq J(st)$. No finiteness assumption is imposed. This closure property gives the multiplicativity of the scalar characters appearing in the band classification.
-- source:
--   On the irreducible representations of a finite semigroup, arXiv:0712.2076v2, PDF p. 7, Lemma 8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P21

namespace QAlgorithms.Papers.Independent.Renew46.P21

universe u v w

/-- Lemma 8, p. 7: for any band, the complement of I_J is a subsemigroup.
The source makes no finiteness assumption in this lemma. -/
theorem band_classIdeal_complement {S : Type v} [Semigroup S]
    (hband : ∀ s : S, s * s = s) (J : JClass S) :
    ∃ T : Subsemigroup S, (T : Set S) = (classIdeal J)ᶜ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P21
