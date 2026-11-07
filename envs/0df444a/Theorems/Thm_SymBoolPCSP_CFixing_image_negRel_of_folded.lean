-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_image_negRel_of_folded
-- name    : SymBoolPCSP.CFixing.image_negRel_of_folded
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:08:58.751193+00:00
-- url     : https://prove2.me/theorems/c948aab7-027f-4f8f-b2c2-fecf45ce391b
-- title:
--   Folded functions commute with negating a relation: f(¬P) = ¬f(P)
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$ be folded, i.e. $f(\bar x) = \overline{f(x)}$ for all $x$. Then for every relation $P \subseteq \{0,1\}^k$,
--
--   $$
--   f(\neg P) = \neg f(P),
--   $$
--
--   where $\neg P = \{\bar x : x \in P\}$ and $\bar x$ is the coordinate-wise negation.
--
--   This is the formal version of "reversing the notions of 0 and 1" at the end of the proof of Claim 4.8 of Brakensiek–Guruswami. For odd $L$ the majority function is folded, so $\mathrm{Maj}(\neg P) = \neg \mathrm{Maj}(P)$. Since $\neg\mathrm{Ham}_k(S) = \mathrm{Ham}_k(k - S)$, any statement about the large-weight part of $\mathrm{Maj}(\mathrm{Ham}_k(S))$ transfers to the small-weight part. The same applies to alternating threshold and parity of odd arity, and to every polymorphism of a folded family.
--
--   **Formalization Note** `IsFolded f` is `∀ x, f x = !f (neg x)`, which is equivalent to the displayed property; `negRel P = neg '' P`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.2, end of the proof of Claim 4.8, p. 19; Definition 2.6, p. 9

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- For a folded `f` (`f(x) = ¬f(x̄)`), images commute with negation: `f(¬P) = ¬f(P)`. -/
theorem image_negRel_of_folded {k L : ℕ} (f : (Fin L → Bool) → Bool) (hf : IsFolded f)
    (P : Set (Fin k → Bool)) : image f (negRel P) = negRel (image f P) := by sorry

end SymBoolPCSP.CFixing
