-- Prove2me | Theorems.Thm_ParityDegreeDepth_Core_binary_descent
-- name    : ParityDegreeDepth.Core.binary_descent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T03:58:42.921605+00:00
-- url     : https://prove2.me/theorems/ad883386-6d26-41aa-ad77-2e5f47100aa5
-- title:
--   Lemma 3.7 (polynomial form): dimension-preserving descent to $\mathbb F_2$
-- statement:
--   Let $T$ be a $(d+1)$-linear form on $\mathbb F_2^n$ with coefficient tensor $c$, extended by the same coefficients. Let $\sigma$ be a finite set of indeterminates and $\Lambda$ an $n\times r$ matrix over the polynomial ring $\mathbb F_2[z_s : s\in\sigma]$ which has a nonzero $r\times r$ minor and whose columns satisfy the strong vanishing identity: for all vectors $x_0,\dots,x_d$ of polynomials such that $x_1,\dots,x_d$ are columns of $\Lambda$,
--
--   $$
--   T(x_0,x_1,\dots,x_d)=0 .
--   $$
--
--   Then there is an $n\times r$ matrix $\Lambda_0$ over $\mathbb F_2$ with a nonzero $r\times r$ minor whose columns satisfy the same identity over $\mathbb F_2$: $T(x_0,x_1,\dots,x_d)=0$ whenever $x_0\in\mathbb F_2^n$ is arbitrary and $x_1,\dots,x_d$ are columns of $\Lambda_0$.
--
--   Equivalently, a $k$-dimensional subspace $U\le K^n$ ($K=\mathbb F_2(z)$) with $T(K^n,U,\dots,U)=0$ yields a binary subspace $U'\le\mathbb F_2^n$ of the same dimension $k$ with $T(\mathbb F_2^n,U',\dots,U')=0$ — Lemma 3.7 of the source, stated with a polynomial basis (any $K$-basis can be scaled to polynomial vectors).
--
--   **Formalization Note** Slot $0$ is the free slot; the remaining $d$ slots carry columns. A nonzero maximal minor is the formal counterpart of the columns being independent over the coefficient field.
-- source:
--   Zhang, Parity Decision Trees of Depth O(4^d log ||f^||_1) for Boolean Functions f of F2-Degree d, STOC 2027 submission #798, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, §3.5, Lemma 3.7 and its proof (normalisation by a minimal-valuation maximal minor, evaluation at z=0, one variable at a time), pp. 9-10

import Mathlib
import Definitions.Def_ParityDegreeDepth_Core_tensorEval

open ParityDegreeDepth.Core

theorem ParityDegreeDepth.Core.binary_descent {σ : Type} [Fintype σ] {n d r : ℕ}
    (c : (Fin (d + 1) → Fin n) → ZMod 2) (Λ : Matrix (Fin n) (Fin r) (MvPolynomial σ (ZMod 2)))
    (hΛ : ∃ ρ : Fin r → Fin n, (Λ.submatrix ρ id).det ≠ 0)
    (hv : ∀ x : Fin (d + 1) → Fin n → MvPolynomial σ (ZMod 2),
      (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λ i l) → tensorEval c x = 0) :
    ∃ Λ₀ : Matrix (Fin n) (Fin r) (ZMod 2), (∃ ρ : Fin r → Fin n, (Λ₀.submatrix ρ id).det ≠ 0) ∧
      ∀ x : Fin (d + 1) → Fin n → ZMod 2,
        (∀ j, j ≠ 0 → ∃ l, x j = fun i => Λ₀ i l) → tensorEval c x = 0 := by sorry
