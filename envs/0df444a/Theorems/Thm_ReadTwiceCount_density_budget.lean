-- Prove2me | Theorems.Thm_ReadTwiceCount_density_budget
-- name    : ReadTwiceCount.density_budget
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:51.485412+00:00
-- url     : https://prove2.me/theorems/42561e94-e953-4954-b784-41421dd772c9
-- title:
--   §7.1 (31)–(32) — child densities $a_i\ge a/(q\sqrt{D_i})$ and $\sum a_i^{-k}\le a^{-k}q^k$
-- statement:
--   Let $E$ be a finite set of EQ boundaries with weights $D_i\ge0$ and $\sum_{i\in E}\sqrt{D_i}\le1$ (21), let $a>0$, $q\ge1$, $s\ge1$ and $k\ge2$, and let the active children form a subset of $E$ with $D_i>0$, $s_i+1\le s$, $\sqrt{D_i}\le r_i\le q\sqrt{D_i}$ and $a_i=\dfrac{as}{r_i(s_i+1)}$ (19). Then for every active child
--   $$a_i=\frac{as}{r_i(s_i+1)}\ge\frac{a}{q\sqrt{D_i}},$$
--   and
--   $$\sum_{i\text{ active}}a_i^{-k}\le a^{-k}q^k\sum_{i\text{ active}}D_i^{k/2}\le a^{-k}q^k\Big(\sum_{i\in E}\sqrt{D_i}\Big)^k\le a^{-k}q^k .$$
--
--   This is the step of the work bound in which the square-root sensitivity budget controls the number of recursive calls.
--
--   Differences from the source:
--   - generalization: $r_i$ a positive dyadic rational and $q=1+1/(10n)$ → $r_i$ any real with $\sqrt{D_i}\le r_i\le q\sqrt{D_i}$ and any $q\ge1$; reason: the displays use only these bounds; the paper's choices satisfy them
--   - reading: "for every active recursive child, (19) and $s_i+1\le s$ … by (21)" → a standalone inequality over a finite family with hypotheses (19), (21), $s_i+1\le s$, $D_i>0$ on active children; reason: an active child fails (18), so $D_i>0$; these are exactly the facts the displays invoke
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §7.1, displays (31)–(32), p.11

import Mathlib

namespace ReadTwiceCount

/-- **The density budget (31)–(32)** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §7.1, displays (31)–(32),
p.11): "For every active recursive child, (19) and sᵢ + 1 ≤ s imply aᵢ = as/(rᵢ(sᵢ + 1)) ≥ a/(q√Dᵢ).
(31) Consequently, by (21), Σ_{i active} aᵢ^{−k} ≤ a^{−k}q^k Σ_{i active} Dᵢ^{k/2} ≤
a^{−k}q^k (Σ_{i∈E} √Dᵢ)^k ≤ a^{−k}q^k." (32)

`E` is the set of EQ boundaries with weights `Dᵢ ≥ 0` and `Σ_{i∈E} √Dᵢ ≤ 1` (21); the active children
form a subset with `Dᵢ > 0`, `sᵢ + 1 ≤ s`, `√Dᵢ ≤ rᵢ ≤ q√Dᵢ` and `aᵢ = as/(rᵢ(sᵢ + 1))` (19).

**Formalization Note** A finite family indexed by any type; `a > 0`, `q ≥ 1`, `k ≥ 2` as in (17) and
(30). -/
theorem density_budget {ι : Type*} (E act : Finset ι) (hact : act ⊆ E) (a q : ℝ) (s k : ℕ)
    (D r ai : ι → ℝ) (si : ι → ℕ) (ha : 0 < a) (hs : 1 ≤ s) (hq : 1 ≤ q) (hk : 2 ≤ k)
    (hD : ∀ i ∈ E, 0 ≤ D i) (hbudget : ∑ i ∈ E, Real.sqrt (D i) ≤ 1)
    (hpos : ∀ i ∈ act, 0 < D i) (hsi : ∀ i ∈ act, si i + 1 ≤ s)
    (hr : ∀ i ∈ act, Real.sqrt (D i) ≤ r i ∧ r i ≤ q * Real.sqrt (D i))
    (hai : ∀ i ∈ act, ai i = a * s / (r i * ((si i : ℝ) + 1))) :
    (∀ i ∈ act, a / (q * Real.sqrt (D i)) ≤ ai i) ∧
      ∑ i ∈ act, (ai i)⁻¹ ^ k ≤ a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) ∧
      a⁻¹ ^ k * q ^ k * ∑ i ∈ act, D i ^ ((k : ℝ) / 2) ≤
        a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k ∧
      a⁻¹ ^ k * q ^ k * (∑ i ∈ E, Real.sqrt (D i)) ^ k ≤ a⁻¹ ^ k * q ^ k := by sorry

end ReadTwiceCount
