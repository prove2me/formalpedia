-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_card_lt_of_subsets_true
-- name    : SymBoolPCSP.CFixing.card_lt_of_subsets_true
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:08:10.522076+00:00
-- url     : https://prove2.me/theorems/2c1564c6-bdfa-4a80-bf4b-db9286ac3fde
-- title:
--   Bounding a set whose m-subsets all evaluate to 1 under a disjoint-family bound
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$, $c, m \in \mathbb{N}$ and $I \subseteq [L]$. Suppose that $f(e_Z) = 1$ for every $Z \subseteq I$ with $|Z| = m$, and that at most $c$ pairwise disjoint sets $S_1, \dots, S_\ell \subseteq [L]$ can satisfy $f(e_{S_i}) = 1$ for all $i$ (that is, any such family has $\ell \le c$). Then $|I| < m(c+1)$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.12, Case 1, p. 24 (with Corollary 4.11)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- If every `m`-element subset `Z ⊆ I` has `f(e_Z) = 1` and at most `c` pairwise disjoint sets
can have `f(e_{S_i}) = 1`, then `|I| < m (c + 1)` (BG, proof of Lemma 4.12, Case 1). -/
theorem card_lt_of_subsets_true {L : ℕ} (f : (Fin L → Bool) → Bool) (c m : ℕ)
    (I : Finset (Fin L)) (hI : ∀ Z ⊆ I, Z.card = m → f (indicator Z) = true)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    I.card < m * (c + 1) := by sorry

end SymBoolPCSP.CFixing
