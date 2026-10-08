-- Prove2me | Theorems.Thm_SymBoolPCSP_Galois_sandwich
-- name    : SymBoolPCSP.Galois.sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:24.164764+00:00
-- url     : https://prove2.me/theorems/ab7bd8ee-fca1-4baf-91ca-388d6c75a294
-- title:
--   §6.1 remark — P′ ⊆ P ⊆ Q ⊆ Q′ makes (P′, Q′) ppp-definable from (P, Q)
-- statement:
--   Let $D$ be a finite domain and let $(P, Q)$ and $(P', Q')$ be relations of the same arity $k$ on $D$. If
--   $$P' \subseteq P \subseteq Q \subseteq Q',$$
--   then the promise relation $(P', Q')$ is ppp-definable from the one-relation family $\{(P, Q)\}$.
--
--   This is the basic way of weakening a promise relation within the ppp-definable closure: shrinking the $P$-side and enlarging the $Q$-side never leaves it. It is the last step of the proof of Theorem 6.1, applied to $P' \subseteq S'_m \subseteq T'_m \subseteq Q'$.
--
--   **Formalization Note** "From $(P, Q)$" is the one-relation family `single P`, `single Q` on the symbol `()`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 27, §6.1, remark after Definition 6.2

import Mathlib
import Definitions.Def_SymBoolPCSP_Galois_Basic

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-- §6.1, p. 27 (after Definition 6.2): if `(P, Q)` and `(P', Q')` have the same arity `k` and
`P' ⊆ P ⊆ Q ⊆ Q'`, then `(P', Q')` is ppp-definable from the one-relation family `{(P, Q)}`. -/
theorem sandwich {D : Type} [Fintype D] [DecidableEq D] {k : ℕ}
    (P Q P' Q' : Set (Fin k → D)) (hP' : P' ⊆ P) (hPQ : P ⊆ Q) (hQ' : Q ⊆ Q') :
    PPPDefinable (single P) (single Q) P' Q' := by sorry

end SymBoolPCSP.Galois
