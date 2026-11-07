-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_card_lt_of_minimal
-- name    : SymBoolPCSP.CFixing.card_lt_of_minimal
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:08:09.744925+00:00
-- url     : https://prove2.me/theorems/8cbeee1b-9a5b-4eec-8f2c-918644e7a41c
-- title:
--   Minimal 1-sets are small under (Ham_{b+r}{1,b+r}, Ham_{b+r}({0..b+r} \ {b}))
-- statement:
--   Let $b \ge 1$, $r \ge 0$ and let $f : \{0,1\}^L \to \{0,1\}$ be a folded polymorphism of the promise relation $\big(\mathrm{Ham}_{b+r}(\{1, b+r\}), \mathrm{Ham}_{b+r}(\{0, \dots, b+r\} \setminus \{b\})\big)$. If $S \subseteq [L]$ is minimal with $f(e_S) = 1$, meaning that $f(e_T) = 0$ for every proper subset $T \subsetneq S$, then $|S| < b$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.12, Case 2, pp. 24–25

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Case 2 of BG Lemma 4.12: let `f` be a folded polymorphism of
`(Ham_{b+r}({1, b+r}), Ham_{b+r}({0, …, b+r} \ {b}))` with `b ≥ 1`. If `S` is minimal with
`f(e_S) = 1` (all proper subsets `T ⊂ S` have `f(e_T) = 0`), then `|S| < b`. -/
theorem card_lt_of_minimal {L b r : ℕ} (f : (Fin L → Bool) → Bool) (hfold : IsFolded f)
    (hb : 1 ≤ b)
    (hpol : PolOf (Ham (b + r) {1, b + r}) (Ham (b + r) (Set.Iic (b + r) \ {b})) f)
    (S : Finset (Fin L)) (hS : f (indicator S) = true)
    (hmin : ∀ T ⊂ S, f (indicator T) = false) :
    S.card < b := by sorry

end SymBoolPCSP.CFixing
