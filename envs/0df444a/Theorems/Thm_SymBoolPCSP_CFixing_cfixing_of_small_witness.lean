-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_cfixing_of_small_witness
-- name    : SymBoolPCSP.CFixing.cfixing_of_small_witness
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T19:08:10.347529+00:00
-- url     : https://prove2.me/theorems/cf7c13c5-3a65-4cc3-a7c5-67164aa28b9e
-- title:
--   Small witnesses plus a disjoint-family bound give a C-fixing function
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$ with $f(0, \dots, 0) = 0$, and let $B, c \in \mathbb{N}$. Suppose that every $X \subseteq [L]$ with $f(e_X) = 1$ contains some $T \subseteq X$ with $f(e_T) = 1$ and $|T| \le B$, and that at most $c$ pairwise disjoint sets $S_1, \dots, S_\ell \subseteq [L]$ can satisfy $f(e_{S_i}) = 1$ for all $i$ (that is, any such family has $\ell \le c$). Then $f$ is $(c+1)B$-fixing: there is $S \subseteq [L]$ with $|S| \le (c+1)B$ such that $f(x) = f(0, \dots, 0)$ for every $x$ vanishing on $S$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, proof of Lemma 4.12, Case 2, p. 25

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- A generic `C`-fixing criterion (BG, proof of Lemma 4.12, Case 2): suppose `f(0) = 0`,
every `X` with `f(e_X) = 1` contains some `T` with `f(e_T) = 1` and `|T| ≤ B`, and at most `c`
pairwise disjoint sets `S_i` can have `f(e_{S_i}) = 1`. Then `f` is `(c + 1) B`-fixing. -/
theorem cfixing_of_small_witness {L : ℕ} (f : (Fin L → Bool) → Bool)
    (h0 : f (fun _ => false) = false) (B c : ℕ)
    (hsmall : ∀ X : Finset (Fin L), f (indicator X) = true →
      ∃ T ⊆ X, f (indicator T) = true ∧ T.card ≤ B)
    (hdisj : ∀ (ℓ : ℕ) (S : Fin ℓ → Finset (Fin L)), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, f (indicator (S i)) = true) → ℓ ≤ c) :
    IsCFixing ((c + 1) * B) f := by sorry

end SymBoolPCSP.CFixing
