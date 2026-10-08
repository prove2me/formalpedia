-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_claim_4_2
-- name    : SymBoolPCSP.CFixing.claim_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:57.739022+00:00
-- url     : https://prove2.me/theorems/888f41ed-aad5-427a-acb7-1e8c73b32fff
-- title:
--   Claim 4.2 — idempotent polymorphisms of (Ham_k(S), Ham_k(T)) drop weight k and arity by one
-- statement:
--   Let $k \ge 1$ and $S \subseteq T \subseteq \{0, \dots, k\}$, and consider the symmetric promise relation $(P, Q) = (\mathrm{Ham}_k(S), \mathrm{Ham}_k(T))$. Every idempotent polymorphism $f$ of $(P, Q)$ is a polymorphism of
--   $$\big(\mathrm{Ham}_{k-1}(S \setminus \{k\}),\ \mathrm{Ham}_{k-1}(T \setminus \{k\})\big).$$
--
--   This lowers the arity of a symmetric promise relation while keeping its idempotent polymorphisms, and is used repeatedly in Lemmas 4.5 and 4.7.
--
--   **Formalization Note** The printed phrase "each idempotent polymorphisms $(P,Q)$" means "each idempotent polymorphism of $(P,Q)$". The hypothesis $k \ge 1$ makes the arity $k - 1$ meaningful.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 16, Claim 4.2

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Claim 4.2 (p. 16): for `P = Ham_k(S) ⊆ Q = Ham_k(T)` with `S ⊆ T ⊆ {0, …, k}` and `k ≥ 1`,
every idempotent polymorphism of `(P, Q)` is a polymorphism of
`(Ham_{k−1}(S ∖ {k}), Ham_{k−1}(T ∖ {k}))`. -/
theorem claim_4_2 {k : ℕ} (hk : 1 ≤ k) (S T : Set ℕ) (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f)
    (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham (k - 1) (S \ {k})) (Ham (k - 1) (T \ {k})) f := by sorry

end SymBoolPCSP.CFixing
