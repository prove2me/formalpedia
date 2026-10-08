-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_claim_4_6
-- name    : SymBoolPCSP.CFixing.claim_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:53.132757+00:00
-- url     : https://prove2.me/theorems/eb416fad-871a-48f1-a255-72aed3a51bb5
-- title:
--   Claim 4.6 — AT(Ham_k(S)) for |S| ≤ 2
-- statement:
--   Write $\mathrm{AT}(P) = \bigcup_{L \text{ odd}} \mathrm{AT}_L(P)$ for the set of all tuples obtained by applying an alternating-threshold function of odd arity coordinate-wise to elements of $P$. Let $k \ge 1$. Then
--
--   1. $\mathrm{AT}(\mathrm{Ham}_k(\{0\})) = \mathrm{Ham}_k(\{0\})$;
--   2. $\mathrm{AT}(\mathrm{Ham}_k(\{k\})) = \mathrm{Ham}_k(\{k\})$;
--   3. $\mathrm{AT}(\mathrm{Ham}_k(\{0,k\})) = \mathrm{Ham}_k(\{0,k\})$;
--   4. if $k \ge 2$ and $\ell \in \{1, \dots, k-1\}$, then $\mathrm{AT}(\mathrm{Ham}_k(\{\ell\})) = \mathrm{Ham}_k(\{1, \dots, k-1\})$;
--   5. if $k \ge 2$ and $\ell_1 \ne \ell_2$ in $\{0, \dots, k\}$ with $\{\ell_1, \ell_2\} \ne \{0, k\}$, then $\mathrm{AT}(\mathrm{Ham}_k(\{\ell_1, \ell_2\})) = \{0,1\}^k$.
--
--   These computations identify which symmetric relations can witness that $\mathrm{AT}_L$ is not a polymorphism, the first step of Lemma 4.5.
--
--   **Formalization Note** In fact 5 the weights $\ell_1, \ell_2$ range over $\{0,\dots,k\}$, the possible Hamming weights, as the source's notation implies.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, p. 17, Claim 4.6 (in the proof of Lemma 4.5)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric

namespace SymBoolPCSP.CFixing

/-- Claim 4.6 (p. 17), with `AT(P) = ⋃_{L odd} AT_L(P)`: for `k ≥ 1`,
1. `AT(Ham_k({0})) = Ham_k({0})`;
2. `AT(Ham_k({k})) = Ham_k({k})`;
3. `AT(Ham_k({0, k})) = Ham_k({0, k})`;
4. `AT(Ham_k({ℓ})) = Ham_k({1, …, k − 1})` for `k ≥ 2`, `ℓ ∈ {1, …, k − 1}`;
5. `AT(Ham_k({ℓ₁, ℓ₂})) = {0,1}^k` for `k ≥ 2`, `ℓ₁ ≠ ℓ₂` in `{0, …, k}`, `{ℓ₁, ℓ₂} ≠ {0, k}`. -/
theorem claim_4_6 (k : ℕ) (hk : 1 ≤ k) :
    ATImage (Ham k {0}) = Ham k {0} ∧
    ATImage (Ham k {k}) = Ham k {k} ∧
    ATImage (Ham k {0, k}) = Ham k {0, k} ∧
    (2 ≤ k → ∀ l : ℕ, 1 ≤ l → l ≤ k - 1 → ATImage (Ham k {l}) = Ham k (Set.Icc 1 (k - 1))) ∧
    (2 ≤ k → ∀ l₁ l₂ : ℕ, l₁ ≤ k → l₂ ≤ k → ({l₁, l₂} : Set ℕ) ≠ {0, k} → l₁ ≠ l₂ →
      ATImage (Ham k {l₁, l₂}) = Set.univ) := by sorry

end SymBoolPCSP.CFixing
