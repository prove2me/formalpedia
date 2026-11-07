-- Prove2me | Theorems.Thm_SymBoolPCSP_CFixing_lemma_4_7_single
-- name    : SymBoolPCSP.CFixing.lemma_4_7_single
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-06T09:39:33.675312+00:00
-- url     : https://prove2.me/theorems/cb726dae-295f-4a98-80eb-a1c762a9997d
-- title:
--   Lemma 4.7 for a single relation: a Maj-violation yields a pinned relaxation
-- statement:
--   Let $S \subseteq T \subseteq \{0,\dots,k\}$. Suppose some $y \in \mathrm{Maj}(\mathrm{Ham}_k(S)) = \bigcup_{L\text{ odd}} \mathrm{Maj}_L(\mathrm{Ham}_k(S))$ has $|y| \notin T$. Then there is $k'$ such that every idempotent folded polymorphism of $(\mathrm{Ham}_k(S), \mathrm{Ham}_k(T))$ is a polymorphism of one of the following:
--
--   - $\big(\mathrm{Ham}_{k'}(\{(k'+1)/2\}), \mathrm{Ham}_{k'}(\{0,\dots,k'-1\})\big)$, with $k' \ge 3$ odd;
--   - $\big(\mathrm{Ham}_{k'}(\{1,k'\}), \mathrm{Ham}_{k'}(\{0,\dots,k'\}\setminus\{b\})\big)$, with $k' \ge 3$ and $2 \le b \le k'-1$.
--
--   This is the single-relation core of Lemma 4.7 of Brakensiek–Guruswami. Let $b = |y|$, $m = \min S$ and $M = \max S$.
--
--   - By Claim 4.8, $2m - k + 1 \le b \le 2M - 1$.
--   - If $b > M$: reduce to $(\{M\}, [0,k]\setminus\{b\})$ and pin, giving arity $k' = 2(b-M)+1$.
--   - If $b < m$: flip and apply the previous case.
--   - Otherwise $b$ lies strictly between two weights $\ell_1 < b < \ell_2$ of $S$ with $\ell_1 \ge 1$ (after flipping if necessary). Pinning $\ell_1 - 1$ ones and $k - \ell_2$ zeros gives the second form.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, §4.2, Lemma 4.7 and its proof, p. 19

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_SymBoolPCSP_CFixing_Basic

open PCSPBLPAff.Symmetric
namespace SymBoolPCSP.CFixing

/-- Lemma 4.7 for a single symmetric promise relation: if `S ⊆ T ⊆ {0,…,k}` and some `y ∈ Maj(Ham_k(S))` has weight outside `T`, then every idempotent folded polymorphism of `(Ham_k(S), Ham_k(T))` is a polymorphism of `(Ham_{k'}({(k'+1)/2}), Ham_{k'}({0,…,k'-1}))` for some odd `k' ≥ 3`, or of `(Ham_{k'}({1,k'}), Ham_{k'}({0,…,k'} ∖ {b}))` for some `k' ≥ 3`, `2 ≤ b ≤ k'-1`. -/
theorem lemma_4_7_single {k : ℕ} {S T : Set ℕ} (hST : S ⊆ T) (hT : T ⊆ Set.Iic k)
    {y : Fin k → Bool} (hy : y ∈ MajImage (Ham k S)) (hyT : hw y ∉ T) :
    ∃ k' : ℕ,
      (3 ≤ k' ∧ Odd k' ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsIdempotent f → IsFolded f →
        PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {(k' + 1) / 2}) (Ham k' (Set.Iic (k' - 1))) f) ∨
      (3 ≤ k' ∧ ∃ b : ℕ, 2 ≤ b ∧ b ≤ k' - 1 ∧ ∀ (L : ℕ) (f : (Fin L → Bool) → Bool),
        IsIdempotent f → IsFolded f → PolOf (Ham k S) (Ham k T) f →
        PolOf (Ham k' {1, k'}) (Ham k' (Set.Iic k' \ {b})) f) := by sorry

end SymBoolPCSP.CFixing
