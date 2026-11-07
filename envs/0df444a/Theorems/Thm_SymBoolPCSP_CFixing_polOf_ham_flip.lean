-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_polOf_ham_flip
-- name    : SymBoolPCSP.CFixing.polOf_ham_flip
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:39:29.565416+00:00
-- url     : https://prove2.me/theorems/9703338e-39f1-4b88-a725-ff76caf450a4
-- title:
--   Folded polymorphisms of (Ham_k(S), Ham_k(T)) are polymorphisms of (Ham_k(k−S), Ham_k(k−T))
-- statement:
--   Let $f : \{0,1\}^L \to \{0,1\}$ be folded and $S \subseteq T$. If $f$ is a polymorphism of $(\mathrm{Ham}_k(S), \mathrm{Ham}_k(T))$, then $f$ is a polymorphism of
--
--   $$
--   \big(\mathrm{Ham}_k(k - S), \mathrm{Ham}_k(k - T)\big), \qquad k - X = \{\ell \le k : k - \ell \in X\}.
--   $$
--
--   This is Claim 4.3 of Brakensiek–Guruswami applied with the full flip set $S = [k]$. Flipping every coordinate maps $\mathrm{Ham}_k(X)$ onto $\mathrm{Ham}_k(k - X)$. It is the precise form of "by symmetry between $0$ and $1$" used in the proofs of Lemmas 4.5 and 4.7.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.1, Claim 4.3, p. 16

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Complementing all coordinates (Claim 4.3 with the full flip set): for folded `f`, `f ∈ Pol(Ham_k(S), Ham_k(T))` implies `f ∈ Pol(Ham_k(k - S), Ham_k(k - T))`. -/
theorem polOf_ham_flip {k L : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (f : (Fin L → Bool) → Bool)
    (hfold : IsFolded f) (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham k {l | l ≤ k ∧ k - l ∈ S}) (Ham k {l | l ≤ k ∧ k - l ∈ T}) f := by sorry

end SymBoolPCSP.CFixing
