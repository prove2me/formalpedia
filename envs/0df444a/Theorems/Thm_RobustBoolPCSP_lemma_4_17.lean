-- Prove2me | Theorems.Thm_RobustBoolPCSP_lemma_4_17
-- name    : RobustBoolPCSP.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:22:02.3822+00:00
-- url     : https://prove2.me/theorems/d97469ea-9f99-4bfa-a6a6-1edb888749c6
-- title:
--   Lemma 4.17 (Alternating Threshold closure)
-- statement:
--   Let $P=\mathrm{Ham}_n(S)$ with $S\subseteq\{0,\dots,n\}$, and suppose $S$ contains an interior weight level $a$, $0<a<n$. The **Alternating Threshold closure** of $P$ is the set of outputs of odd $\mathrm{AT}_L$ applied coordinatewise to $L$ tuples of $P$, over all odd $L$.
--
--   1. If $S=\{a\}$, the closure consists of all nonconstant tuples.
--   2. If $|S|\ge2$, the closure is $\{0,1\}^n$.
--
--   Together with Lemma 4.16 this decides which family preserves a symmetric pair.
--
--   Differences from the source:
--   - encoding: tuples in sign notation {−1, 1}^n, weight = number of +1 entries → Boolean tuples Fin n → Bool with true = +1, weight hw = number of true entries; sums use sgnVec; reason: the identification 0 ↔ −1, 1 ↔ +1 of §3.2
--   - reading: P = Ham_n(S), |S| ≥ 2 → S ⊆ {0, …, n}; reason: Ham_r(S) is defined for S ⊆ {0, …, r} (p.15), so |S| counts weight levels
--   - encoding: nonconstant tuples → tuples with two coordinates that differ; reason: definition
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.17, p.25

import Mathlib
import Definitions.Def_SymBoolPCSP_CFixing_Basic

set_option autoImplicit false

namespace RobustBoolPCSP

open SymBoolPCSP.CFixing in
/-- **Lemma 4.17 (Alternating Threshold closure)**, p.25. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let P = Ham_n(S) contain an interior weight level a, 0 < a < n. If S = {a}, the Alternating
Threshold closure of P consists of all nonconstant tuples. If |S| ≥ 2, it is {−1, 1}^n."

**Formalization Note.** The Alternating Threshold closure is the published `ATImage` (outputs of
every odd `AT_L`). `S` is a finite set of weights with `S ⊆ {0, …, n}` (the convention of
`Ham_n(S)`, p.15), so `|S|` counts weight levels of `{0,1}^n`. A tuple is nonconstant when two of
its coordinates differ. -/
theorem lemma_4_17 (n : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, s ≤ n) (a : ℕ) (ha : a ∈ S)
    (ha0 : 0 < a) (han : a < n) :
    (S = {a} → ATImage (Ham n ↑S) = {x | ∃ i j, x i ≠ x j}) ∧
    (2 ≤ S.card → ATImage (Ham n ↑S) = Set.univ) := by sorry

end RobustBoolPCSP
