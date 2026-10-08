-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_claim_4_8
-- name    : SymBoolPCSP.CFixing.claim_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:30.967358+00:00
-- url     : https://prove2.me/theorems/1087fc53-5a32-43fc-9662-5fb83cee4835
-- title:
--   Claim 4.8 — Maj(Ham_k(S)) is Ham_k of an interval
-- statement:
--   Write $\mathrm{Maj}(P) = \bigcup_{L \text{ odd}} \mathrm{Maj}_L(P)$. Let $k \ge 1$.
--
--   1. If $P \subseteq \mathrm{Ham}_k(\{0, k\})$, then $\mathrm{Maj}(P) = P$.
--   2. If $P = \mathrm{Ham}_k(S)$ with $S \subseteq \{0, \dots, k\}$ and $S \setminus \{0, k\} \ne \emptyset$, then
--   $$\mathrm{Maj}(P) = \mathrm{Ham}_k\big(\{0, \dots, k\} \cap \{2(\min S) - k + 1, \dots, 2(\max S) - 1\}\big).$$
--
--   This is the majority analogue of Claim 4.6, the first step of Lemma 4.7.
--
--   **Formalization Note** The interval bounds are computed in $\mathbb{Z}$, since $2(\min S) - k + 1$ can be negative. $S$ is a finite set of weights in $\{0, \dots, k\}$, the setting in which $\min S$ and $\max S$ are the extreme weights of $P$; its nonemptiness is a binder only so that $\min S$ and $\max S$ are defined (it follows from $S \setminus \{0,k\} \ne \emptyset$).
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 19, Claim 4.8 (in the proof of Lemma 4.7)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Claim 4.8 (p. 19), with `Maj(P) = ⋃_{L odd} Maj_L(P)`: for `k ≥ 1`, if `P ⊆ Ham_k({0, k})` then
`Maj(P) = P`; and if `P = Ham_k(S)` with `S ⊆ {0, …, k}` and `S ∖ {0, k} ≠ ∅`, then
`Maj(P) = Ham_k({0, …, k} ∩ {2(min S) − k + 1, …, 2(max S) − 1})` (bounds computed in `ℤ`). -/
theorem claim_4_8 (k : ℕ) (hk : 1 ≤ k) :
    (∀ P : Set (Fin k → Bool), P ⊆ Ham k {0, k} → MajImage P = P) ∧
    (∀ (S : Finset ℕ) (hne : S.Nonempty), (∀ s ∈ S, s ≤ k) → (S \ {0, k}).Nonempty →
      MajImage (Ham k (S : Set ℕ)) =
        Ham k {b : ℕ | b ≤ k ∧ 2 * (S.min' hne : ℤ) - k + 1 ≤ b ∧
          (b : ℤ) ≤ 2 * (S.max' hne : ℤ) - 1}) := by sorry

end SymBoolPCSP.CFixing
