-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_image_subset_of_conservative
-- name    : SymBoolPCSP.CFixing.image_subset_of_conservative
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:08:54.97809+00:00
-- url     : https://prove2.me/theorems/6db458b0-c67b-4a01-a2ac-506c70555d79
-- title:
--   Conservative functions map relations of constant tuples into themselves
-- statement:
--   Call $f : \{0,1\}^L \to \{0,1\}$ *conservative* if for every $v$ the value $f(v)$ equals one of the entries $v_1,\dots,v_L$. Let $P \subseteq \mathrm{Ham}_k(\{0,k\})$, i.e. every tuple of $P$ is constant ($0^k$ or $1^k$). Then
--
--   $$
--   f(P) \subseteq P .
--   $$
--
--   Indeed, all columns of a matrix with constant rows equal one vector $v$, so the output is the constant tuple with value $f(v)$, which is one of the rows. Odd-arity majority and alternating-threshold functions are conservative; this gives the cases $\mathrm{AT}(P) = P$ and $\mathrm{Maj}(P) = P$ for $P \subseteq \mathrm{Ham}_k(\{0,k\})$ in Claims 4.6 and 4.8 of Brakensiek–Guruswami. The lemma applies to any conservative operation, e.g. any symmetric threshold function of odd arity.
--
--   **Formalization Note** $f(P)$ is `image f P` (Definition 2.7); conservativity is `∀ v, ∃ l, f v = v l`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.2, Claim 4.6 (parts 1–3) and Claim 4.8 (first case), pp. 17–19

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- A conservative function (`f(v)` is always one of the entries of `v`) maps every relation consisting of constant tuples into itself: `f(P) ⊆ P` whenever `P ⊆ Ham_k({0, k})`. -/
theorem image_subset_of_conservative {k L : ℕ} (f : (Fin L → Bool) → Bool)
    (hf : ∀ v, ∃ l, f v = v l) (P : Set (Fin k → Bool)) (hP : P ⊆ Ham k {0, k}) :
    image f P ⊆ P := by sorry

end SymBoolPCSP.CFixing
