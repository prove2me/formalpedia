-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_proposition_2_15
-- name    : SymBoolPCSP.CFixing.proposition_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:55.261392+00:00
-- url     : https://prove2.me/theorems/5ed87dde-4a50-4e67-b473-8547aee4efde
-- title:
--   Proposition 2.15 — f(P) is symmetric when P is
-- statement:
--   Let $P \subseteq \{0,1\}^k$ be a symmetric relation and let $f : \{0,1\}^L \to \{0,1\}$ be any function. Then the relation
--   $$f(P) = \{(f(x^{(1)}_1,\dots,x^{(L)}_1), \dots, f(x^{(1)}_k,\dots,x^{(L)}_k)) : x^{(1)},\dots,x^{(L)} \in P\}$$
--   is symmetric.
--
--   Consequently $f(P)$ is a union of sets $\mathrm{Ham}_k(\{a\})$, which is how the relaxation lemmas read off Hamming weights.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 12, Proposition 2.15

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Proposition 2.15 (p. 12): if `P` is symmetric, then `f(P)` is symmetric for every
`f : {0,1}^L → {0,1}`. -/
theorem proposition_2_15 {k L : ℕ} (P : Set (Fin k → Bool)) (hP : IsSymmetricRel P)
    (f : (Fin L → Bool) → Bool) : IsSymmetricRel (image f P) := by sorry

end SymBoolPCSP.CFixing
