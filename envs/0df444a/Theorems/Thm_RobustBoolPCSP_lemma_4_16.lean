-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_16
-- name    : RobustBoolPCSP.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:43.531649+00:00
-- url     : https://prove2.me/theorems/a58fa10b-d7a1-4718-87cd-07e2a18576b1
-- title:
--   Lemma 4.16 (Majority closure) — convex-hull criterion and the closure of a weight level (corrected: n ≥ 1 in the second sentence)
-- statement:
--   Use sign notation ($0\mapsto-1$, $1\mapsto+1$); the weight of a tuple is its number of $+1$ entries, and the **Majority closure** of $P\subseteq\{-1,1\}^n$ is the set of outputs of odd $\mathrm{Maj}_L$ applied coordinatewise to $L$ tuples of $P$, over all odd $L$.
--
--   1. For every $P\subseteq\{-1,1\}^n$, a sign tuple $\sigma$ lies in the Majority closure of $P$ if and only if
--   $$\mathrm{conv}(P)\cap\{z\in\mathbb R^n:\ \sigma_iz_i>0\ \text{for all } i\}\neq\emptyset.$$
--   2. Let $n\ge1$ and $0\le\beta\le n$, and $P=\mathrm{Ham}_n(\{\beta\})$. A tuple of weight $j$ lies in the Majority closure of $P$ exactly when $j/2<\beta<(n+j)/2$ if $1\le j\le n-1$, when $\beta<n/2$ if $j=0$, and when $\beta>n/2$ if $j=n$.
--   3. If $P$ is symmetric, contains a tuple of some interior weight $a$ ($0<a<n$), and contains tuples of weights $s<n/2<s'$, then its Majority closure is $\{-1,1\}^n$.
--
--   An odd-arity Majority family preserves $(P,Q)$ exactly when the closure lies in $Q$, so the lemma decides Majority preservation for symmetric pairs.
--
--   Differences from the source:
--   - encoding: tuples in sign notation {−1, 1}^n, weight = number of +1 entries → Boolean tuples Fin n → Bool with true = +1, weight hw = number of true entries; sums use sgnVec; reason: the identification 0 ↔ −1, 1 ↔ +1 of §3.2
--   - correction: the second sentence for every n → it assumes 1 ≤ n; reason: at n = 0 the clauses for j = 0 and j = n contradict each other: P = Ham_0({0}) = {()} has Majority closure {()}, the empty tuple has weight 0 = n, and the j = 0 condition β < n/2 = 0 fails
--   - reading: P = Ham_n({β}) → β ≤ n; reason: Ham_r(S) is defined for S ⊆ {0, …, r} (p.15)
--   - reading: P contains an interior weight level and levels s < n/2 < s′ → P contains a tuple of an interior weight a and tuples of weights s < n/2 < s′; reason: for symmetric P a tuple of weight w in P means the whole level w lies in P
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.16, p.24

import Mathlib
import Definitions.Def_RobustBoolPCSP_SDP

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Lemma 4.16 (Majority closure)**, p.24. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"For every P ⊆ {−1, 1}^n, a sign tuple σ lies in the Majority closure of P if and only if the
convex hull of P meets the open orthant {z : σi zi > 0 for all i}. For P = Ham_n({β}), a tuple of
weight j lies in the closure exactly when j/2 < β < (n + j)/2 for 1 ≤ j ≤ n − 1, when β < n/2 for
j = 0, and when β > n/2 for j = n. If P is symmetric and contains an interior weight level and
levels s < n/2 < s′, its Majority closure is {−1, 1}^n."

**Formalization Note.** Tuples are Boolean (`true` = +1, the weight `hw` counts `true` entries); the
Majority closure is the published `MajImage` (outputs of every odd `Maj_L`, `L = 1` included); the
convex hull is taken in `ℝ^n` of the sign vectors `sgnVec x`. The second sentence assumes `1 ≤ n`
(correction: at `n = 0` its clauses for `j = 0` and `j = n` contradict each other) and `β ≤ n`
(the convention `S ⊆ {0, …, n}` of `Ham_n(S)`, p.15). "Contains a level `s`" means some tuple of
`P` has weight `s`; for symmetric `P` this is the whole level. -/
theorem lemma_4_16 :
    (∀ (n : ℕ) (P : Set (Fin n → Bool)) (σ : Fin n → Bool),
      σ ∈ MajImage P ↔
        ∃ z ∈ convexHull ℝ (sgnVec '' P), ∀ i, 0 < sgn (σ i) * z i) ∧
    (∀ (n β : ℕ), 1 ≤ n → β ≤ n → ∀ x : Fin n → Bool,
      (1 ≤ hw x → hw x ≤ n - 1 →
        (x ∈ MajImage (Ham n {β}) ↔
          (hw x : ℝ) / 2 < β ∧ (β : ℝ) < ((n : ℝ) + hw x) / 2)) ∧
      (hw x = 0 → (x ∈ MajImage (Ham n {β}) ↔ (β : ℝ) < (n : ℝ) / 2)) ∧
      (hw x = n → (x ∈ MajImage (Ham n {β}) ↔ (n : ℝ) / 2 < β))) ∧
    (∀ (n : ℕ) (P : Set (Fin n → Bool)), IsSymmetricRel P →
      (∃ a : ℕ, 0 < a ∧ a < n ∧ ∃ x ∈ P, hw x = a) →
      (∃ s s' : ℕ, 2 * s < n ∧ n < 2 * s' ∧ (∃ x ∈ P, hw x = s) ∧ (∃ x ∈ P, hw x = s')) →
      MajImage P = Set.univ) := by sorry

end RobustBoolPCSP
