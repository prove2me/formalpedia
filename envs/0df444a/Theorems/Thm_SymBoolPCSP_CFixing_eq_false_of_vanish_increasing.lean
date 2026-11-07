-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_eq_false_of_vanish_increasing
-- name    : SymBoolPCSP.CFixing.eq_false_of_vanish_increasing
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:08:10.473551+00:00
-- url     : https://prove2.me/theorems/e2b26300-2a5b-47e8-8d01-ed86eff3c1b1
-- title:
--   A Boolean function vanishing at 0 vanishes off its somewhere-increasing coordinates
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$ with $f(0, \dots, 0) = 0$. Call a coordinate $j \in [L]$ *somewhere-increasing* for $f$ if there is $Y \subseteq [L]$ with $j \notin Y$, $f(e_Y) = 0$ and $f(e_{Y \cup \{j\}}) = 1$, where $e_Y$ is the indicator vector of $Y$. Let $I$ be the set of somewhere-increasing coordinates. Then $f(x) = 0$ for every $x \in \{0,1\}^L$ with $x_i = 0$ for all $i \in I$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.12, Case 1, p. 24

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- If `f(0) = 0`, then `f(x) = 0` for every `x` vanishing on the set of coordinates on which
`f` is somewhere-increasing, i.e. the `j` with `f(e_Y) = 0`, `f(e_{Y ∪ {j}}) = 1` for some
`Y ∌ j` (BG, proof of Lemma 4.12, Case 1). -/
theorem eq_false_of_vanish_increasing {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (x : Fin L → Bool)
    (hx : ∀ i ∈ Finset.univ.filter (fun j : Fin L => ∃ Y : Finset (Fin L), j ∉ Y ∧
      f (indicator Y) = false ∧ f (indicator (insert j Y)) = true), x i = false) :
    f x = false := by sorry

end SymBoolPCSP.CFixing
