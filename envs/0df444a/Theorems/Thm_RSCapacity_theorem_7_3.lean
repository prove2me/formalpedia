-- Prove2me | Theorems.Thm_RSCapacity_theorem_7_3
-- name    : RSCapacity.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:29:11.430464+00:00
-- url     : https://prove2.me/theorems/c8a0ebc1-a54b-4d54-9d37-050abcb692c5
-- title:
--   Theorem 7.3 (A sparse list bound from a differential interpolant)
-- statement:
--   Fix $r,B\ge0$. There is a constant $C_{r,B}$ such that the following holds. Let $\mathbb F_q$ be a finite field of characteristic $p>\max\{k-1,B\}$, let $D=\{\alpha_1,\dots,\alpha_n\}\subseteq\mathbb F_q$ have $n$ distinct points, let $S_i\subseteq\mathbb F_q$ have total incidence $M$, and let $A\ge k\ge1$. Suppose every $P\in\mathcal L(D,k,\mathbf S,A)$ satisfies $Q(X,P,P^{[1]},\dots,P^{[r]})\equiv0$ for a nonzero polynomial $Q$ with $\deg_XQ\le D_0$, $\deg^{\mathrm{tot}}_YQ\le B$ and $D_0\ge2$. Then
--   $$|\mathcal L(D,k,\mathbf S,A)|\ \le\ C_{r,B}\,(D_0+k)\,k^r\,\max\Bigl\{1,\frac{M}{A-k+1}\Bigr\}^r .$$
--   If $M=0$, the list is empty.
--
--   The bound does not depend on the field size $q$; with $M\le Ln$ and $A-k+1\ge\gamma n$ it gives the polynomial list size of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the effective constant C_{r,B} → a natural number chosen after r, B and before the field and the instance; reason: a real constant can be rounded up
--   - encoding: |ℒ(D, k, 𝐒, A)| → Set.ncard of ℒ, a finite set (polynomials of degree below k over a finite field); reason: no instance changes
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 7.3, p.30 (PDF 32)

import Mathlib
import Definitions.Def_RSCapacity_ListRecovery
import Definitions.Def_RSCapacity_DiffSubst

open Polynomial

set_option autoImplicit false

namespace RSCapacity

/-- **Theorem 7.3 (A sparse list bound from a differential interpolant).** Jeronimo,
arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Theorem 7.3, p.30 (PDF 32).
Fix r, B ≥ 0, and let 𝔽_q be a finite field of characteristic p > max{k − 1, B}. Let
D = {α_1, …, α_n} ⊆ 𝔽_q have n distinct points, let S_i ⊆ 𝔽_q have total incidence M, and let
A ≥ k ≥ 1. Suppose every P ∈ ℒ(D, k, 𝐒, A) satisfies Q(X, P, P^{[1]}, …, P^{[r]}) ≡ 0 for a nonzero
polynomial Q with deg_X Q ≤ D_0, deg^tot_Y Q ≤ B, and D_0 ≥ 2. Then, for an effective constant
C_{r,B}, |ℒ(D, k, 𝐒, A)| ≤ C_{r,B} (D_0 + k) k^r max{1, M/(A − k + 1)}^r (69). If M = 0, the list is
empty.

**Formalization Note.** C_{r,B} is a natural number chosen after r, B and before the field and the
instance. 𝔽_q is any finite field (`Fintype F`, not necessarily prime). |ℒ| is `Set.ncard`; ℒ is a
set of polynomials of degree below k over a finite field, hence finite. -/
theorem theorem_7_3 (r B : ℕ) :
    ∃ C : ℕ, ∀ (F : Type) [Field F] [Fintype F] (k : ℕ), k - 1 < ringChar F →
      B < ringChar F → ∀ (n : ℕ) (α : Fin n → F), Function.Injective α →
      ∀ (S : Fin n → Finset F) (A : ℕ), 1 ≤ k → k ≤ A →
      ∀ (Q : MvPolynomial (Fin (r + 2)) F) (D₀ : ℕ), Q ≠ 0 → Q.degreeOf 0 ≤ D₀ →
        Q.weightedTotalDegree (yWeight r) ≤ B → 2 ≤ D₀ →
        (∀ P ∈ listSet α k S A, diffEval Q P = 0) →
        ((listSet α k S A).ncard : ℝ) ≤
            C * ((D₀ : ℝ) + k) * (k : ℝ) ^ r *
              max 1 ((incidence S : ℝ) / ((A : ℝ) - k + 1)) ^ r ∧
          (incidence S = 0 → listSet α k S A = ∅) := by sorry

end RSCapacity
