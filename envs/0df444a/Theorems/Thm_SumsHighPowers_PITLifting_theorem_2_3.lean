-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_3
-- name    : SumsHighPowers.PITLifting.theorem_2_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T16:10:11.824069+00:00
-- url     : https://prove2.me/theorems/ce890da8-d8eb-435b-8097-bc151c17198b
-- title:
--   Theorem 2.3 — Wronskian criterion for linear dependence of polynomials in characteristic 0 or $p>d$
-- statement:
--   Let $F$ be a field of characteristic $p$, and let $g_1,\dots,g_n\in F[x]$ be polynomials of degree at most $d$. Their **Wronskian** is the determinant
--   $$W(g_1,\dots,g_n)=\det\big(\nabla^{(i)}g_j\big)_{0\le i\le n-1,\ 1\le j\le n},\qquad \nabla^{(i)}=\tfrac{d^i}{dx^i}\ \text{(formal derivative)}.$$
--   If $p=0$ or $p>d$, then
--   $$g_1,\dots,g_n \text{ are linearly dependent over } F\iff W(g_1,\dots,g_n)\equiv 0 .$$
--
--   The characteristic bound is needed: in characteristic $p$, $x^p$ and $1$ are linearly independent but their Wronskian is $0$. The criterion is the tool behind the ABC theorems of §2.3 (Theorem 2.7) and the differential-operator method of §2. The paper proves it in Appendix A (p. 78).
--
--   **Formalization Note.** The Wronskian is the published `BorderDiffEq.wronskian` (rows $f_i$, column $j$ holds the $j$-th derivative), the transpose of the paper's matrix (3); "maximum degree $d$" is `∀ i, (g i).natDegree ≤ d`.
--
--   Differences from the source:
--   - encoding: g_1, …, g_n linearly dependent over F → `¬ LinearIndependent F g` for `g : Fin n → F[X]`; reason: the family (list) sense of linear dependence, indexed by Fin n
--   - encoding: the maximum degree of any g_i is d → `∀ i, (g i).natDegree ≤ d`; reason: the two forms are equivalent statements: given the bound form, take d = the maximum degree; given the exact form, p > d ≥ max_i deg g_i lets it be applied with the maximum
--   - encoding: W(g_1, …, g_n) = det of the matrix (3) with (i, j)-entry ∇^(i) g_j → the published `BorderDiffEq.wronskian g` = det of `(derivative^[j] (g i))`; reason: the transpose of the paper's matrix, which has the same determinant
--   - encoding: F of characteristic p with p = 0 or p > d → `ringChar F = 0 ∨ d < ringChar F`; reason: the characteristic of a field is 0 or a prime p, and `ringChar F` is that number
--   - encoding: a field F → `F : Type` (universe 0); reason: the published `BorderDiffEq.wronskian` is stated for `A : Type`; every field of interest lives in Type
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 15, Theorem 2.3 (proof: Appendix A, p. 78)

import Mathlib
import Definitions.Def_BorderDiffEq_wronskian

namespace SumsHighPowers.PITLifting

/-- **Theorem 2.3** (Kaplan–Shpilka–Tal, p. 15; proof in Appendix A, p. 78). Let `g₁, …, gₙ` be
polynomials over a field `F` of characteristic `p`. If the maximum degree of any `gᵢ` is `d` and
`p = 0` or `p > d`, then `g₁, …, gₙ` are linearly dependent over `F` if and only if their Wronskian
`W(g₁, …, gₙ)` is identically zero. -/
theorem theorem_2_3 {F : Type} [Field F] {n : ℕ} (g : Fin n → Polynomial F) (d : ℕ)
    (hdeg : ∀ i, (g i).natDegree ≤ d)
    (hchar : ringChar F = 0 ∨ d < ringChar F) :
    ¬ LinearIndependent F g ↔ BorderDiffEq.wronskian g = 0 := by sorry

end SumsHighPowers.PITLifting
