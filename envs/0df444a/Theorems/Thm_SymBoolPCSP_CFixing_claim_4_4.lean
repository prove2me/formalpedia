-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_claim_4_4
-- name    : SymBoolPCSP.CFixing.claim_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:15.153275+00:00
-- url     : https://prove2.me/theorems/09d408bd-f9f9-4947-b06d-27e22e509668
-- title:
--   Claim 4.4 — idempotent folded polymorphisms survive shifting the weights down by one
-- statement:
--   Let $k \ge 1$ and $S \subseteq T \subseteq \{0, \dots, k\}$, and consider $(P, Q) = (\mathrm{Ham}_k(S), \mathrm{Ham}_k(T))$. Every idempotent, folded polymorphism of $(P, Q)$ is a polymorphism of
--   $$\big(\mathrm{Ham}_{k-1}(\{\ell \ge 0 : \ell + 1 \in S\}),\ \mathrm{Ham}_{k-1}(\{\ell \ge 0 : \ell + 1 \in T\})\big).$$
--
--   Together with Claim 4.2 it reduces a symmetric promise relation to the small canonical relations listed in Lemmas 4.5 and 4.7.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 17, Claim 4.4

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Claim 4.4 (p. 17): for `P = Ham_k(S) ⊆ Q = Ham_k(T)` with `S ⊆ T ⊆ {0, …, k}` and `k ≥ 1`,
every idempotent, folded polymorphism of `(P, Q)` is a polymorphism of
`(Ham_{k−1}({ℓ ≥ 0 : ℓ + 1 ∈ S}), Ham_{k−1}({ℓ ≥ 0 : ℓ + 1 ∈ T}))`. -/
theorem claim_4_4 {k : ℕ} (hk : 1 ≤ k) (S T : Set ℕ) (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {L : ℕ} (f : (Fin L → Bool) → Bool) (hidem : IsIdempotent f) (hfold : IsFolded f)
    (hf : PolOf (Ham k S) (Ham k T) f) :
    PolOf (Ham (k - 1) {l | l + 1 ∈ S}) (Ham (k - 1) {l | l + 1 ∈ T}) f := by sorry

end SymBoolPCSP.CFixing
