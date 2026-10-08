-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_proposition_2_12
-- name    : SymBoolPCSP.CFixing.proposition_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:38.404798+00:00
-- url     : https://prove2.me/theorems/3491dce6-126f-4a20-a4a8-f4ecb3a93803
-- title:
--   Proposition 2.12 — a non-degenerate, non-idempotent f makes (P, ¬Q) a promise relation with ¬f idempotent
-- statement:
--   Let $(P, Q)$ be a Boolean promise relation of arity $k$ (so $P \subseteq Q$), and let $f : \{0,1\}^L \to \{0,1\}$ be a polymorphism of $(P,Q)$ that is non-degenerate ($f(0,\dots,0) \ne f(1,\dots,1)$) and not idempotent. Write $\neg Q = \{\bar x : x \in Q\}$. Then
--   $$P \subseteq \neg Q, \qquad \neg f \text{ is idempotent}, \qquad \neg f \in \mathrm{Pol}(P, \neg Q).$$
--
--   This is what allows non-idempotent polymorphisms to be traded for idempotent polymorphisms of the negated family.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 11, Proposition 2.12

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Proposition 2.12 (p. 11): if the promise relation `(P, Q)` has a non-degenerate,
non-idempotent polymorphism `f`, then `(P, ¬Q)` is a promise relation and `¬f` is an idempotent
polymorphism of it. -/
theorem proposition_2_12 {k L : ℕ} (P Q : Set (Fin k → Bool)) (hPQ : P ⊆ Q)
    (f : (Fin L → Bool) → Bool) (hf : PolOf P Q f) (hnd : IsNonDegenerate f)
    (hni : ¬ IsIdempotent f) :
    P ⊆ negRel Q ∧ IsIdempotent (fun x => !f x) ∧ PolOf P (negRel Q) (fun x => !f x) := by sorry

end SymBoolPCSP.CFixing
