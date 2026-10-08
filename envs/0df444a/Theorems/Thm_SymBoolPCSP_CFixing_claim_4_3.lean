-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_claim_4_3
-- name    : SymBoolPCSP.CFixing.claim_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:39.037965+00:00
-- url     : https://prove2.me/theorems/9e74cd04-ae66-4d4e-88f7-20a8660fcd85
-- title:
--   Claim 4.3 — (P, Q) and (flip_S(P), flip_S(Q)) have the same folded polymorphisms
-- statement:
--   Let $(P, Q)$ be a Boolean promise relation of arity $k$ and $S \subseteq \{1,\dots,k\}$, and let $\mathrm{flip}_S(P) = \{y : y \oplus e_S \in P\}$. For every folded $f : \{0,1\}^L \to \{0,1\}$,
--   $$f \in \mathrm{Pol}(P, Q) \iff f \in \mathrm{Pol}(\mathrm{flip}_S(P), \mathrm{flip}_S(Q)).$$
--
--   With $S = [k]$ this says that $(P,Q)$ and $(\neg P, \neg Q)$ have the same folded polymorphisms, which lets the proofs exchange the roles of $0$ and $1$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 16, Claim 4.3

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Claim 4.3 (p. 16): for a promise relation `(P, Q)` of arity `k` and `S ⊆ [k]`, the folded
polymorphisms of `(P, Q)` and of `(flip_S(P), flip_S(Q))` coincide. -/
theorem claim_4_3 {k L : ℕ} (P Q : Set (Fin k → Bool)) (hPQ : P ⊆ Q) (S : Finset (Fin k))
    (f : (Fin L → Bool) → Bool) (hfold : IsFolded f) :
    PolOf P Q f ↔ PolOf (flipRel S P) (flipRel S Q) f := by sorry

end SymBoolPCSP.CFixing
