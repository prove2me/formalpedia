-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_5_single
-- name    : SymBoolPCSP.CFixing.lemma_4_5_single
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:39:28.768594+00:00
-- url     : https://prove2.me/theorems/69a9224c-ca4c-438c-9f2b-e0aac26f0ed4
-- title:
--   Lemma 4.5 for a single relation: an AT-violation yields a pinned relaxation
-- statement:
--   Let $S \subseteq T \subseteq \{0,\dots,k\}$. Suppose some $y \in \mathrm{AT}(\mathrm{Ham}_k(S)) = \bigcup_{L\text{ odd}} \mathrm{AT}_L(\mathrm{Ham}_k(S))$ has $|y| \notin T$, i.e. some odd alternating threshold function fails to be a polymorphism of $(\mathrm{Ham}_k(S), \mathrm{Ham}_k(T))$. Then there is $k'$ such that every idempotent folded polymorphism of $(\mathrm{Ham}_k(S), \mathrm{Ham}_k(T))$ is a polymorphism of one of the following:
--
--   - $\big(\mathrm{Ham}_{k'}(\{1\}), \mathrm{Ham}_{k'}(\{0,\dots,k'-2, k'\})\big)$, with $k' \ge 3$;
--   - $\big(\mathrm{Ham}_{k'}(\{0,b\}), \mathrm{Ham}_{k'}(\{0,\dots,k'-1\})\big)$, with $k' \ge 2$ and $1 \le b \le k'-1$.
--
--   This is the single-relation core of Lemma 4.5 of Brakensiek–Guruswami. Let $b = |y|$.
--
--   - By conservativity, $S$ contains some $\ell$ with $1 \le \ell \le k-1$.
--   - If $1 \le b \le k-1$: reduce to $(\{\ell\}, [0,k]\setminus\{b\})$ and pin $k-b-1$ zeros and $\ell-1$ ones. When $\ell > b$, flip all coordinates first.
--   - If $b = k$: Claim 4.6 forces a second weight $\ell' \in S$, and pinning $\min(\ell, \ell')$ ones gives the second form.
--   - If $b = 0$: flip to the case $b = k$.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.2, Lemma 4.5 and its proof, pp. 17–18

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Lemma 4.5 for a single symmetric promise relation: if `S ⊆ T ⊆ {0,…,k}` and some `y ∈ AT(Ham_k(S))` has weight outside `T`, then every idempotent folded polymorphism of `(Ham_k(S), Ham_k(T))` is a polymorphism of `(Ham_{k'}({1}), Ham_{k'}({0,…,k'-2,k'}))` for some `k' ≥ 3`, or of `(Ham_{k'}({0,b}), Ham_{k'}({0,…,k'-1}))` for some `k' ≥ 2`, `1 ≤ b ≤ k'-1`. -/
theorem lemma_4_5_single {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ ATImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f → PolOf (Ham k' {1}) (Ham k' (Set.Iic (k' - 2) ∪ {k'})) f) ∨
      (2 ≤ k' ∧ ∃ b : ℕ, 1 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {0, b}) (Ham k' (Set.Iic (k' - 1))) f) := by sorry

end SymBoolPCSP.CFixing
