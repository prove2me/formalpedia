-- Prove2me | Theorems.Thm_SubspaceTheorem_p_adic_subspace_theorem
-- name    : SubspaceTheorem.p_adic_subspace_theorem
-- status  : Open
-- author  : @Shiv__0
-- created : 2026-11-27T06:43:53.45345+00:00
-- url     : https://prove2.me/theorems/fce873f8-d594-4fb4-8f8a-e6c58c6ee72d
-- title:
--   Schlickewei's $p$-adic Subspace Theorem
-- statement:
--   Let $n \ge 2$ be an integer and let $S$ be a finite set of prime numbers. Suppose $L_{1,\infty}, \dots, L_{n,\infty}$ are $n$ linearly independent linear forms in $n$ variables with real algebraic coefficients, and for each prime $p \in S$, suppose $L_{1,p}, \dots, L_{n,p}$ are $n$ linearly independent linear forms in $n$ variables with $p$-adic coefficients in $\mathbb{Q}_p$ that are algebraic over $\mathbb{Q}$. Then for every real number $\delta > 0$, all nonzero integer solutions $\mathbf{x} = (x_1, \dots, x_n) \in \mathbb{Z}^n \setminus \{\mathbf{0}\}$ to the inequality
--
--   $$
--   \Biggl(\prod_{i=1}^{n} |L_{i,\infty}(\mathbf{x})|\Biggr)\,\Biggl(\prod_{p \in S} \prod_{i=1}^{n} |L_{i,p}(\mathbf{x})|_p\Biggr) \;<\; \|\mathbf{x}\|_{\infty}^{-\delta}
--   $$
--
--   lie in the union of finitely many proper linear subspaces of $\mathbb{Q}^n$, where $|\cdot|_p$ denotes the normalized $p$-adic absolute value ($|p|_p = p^{-1}$) and $\|\mathbf{x}\|_{\infty} = \max_{1 \le j \le n} |x_j|$.
--
--   This is Schlickewei's $p$-adic generalization of Wolfgang Schmidt's Subspace Theorem. It is a central foundational tool in Diophantine approximation and transcendence theory, yielding finiteness results for $S$-unit equations, non-degenerate linear recurrence sequences, and combinatorial transcendence criteria for algebraic digit expansions.
--
--   **Formalization Note** Linear independence of each system of $n$ linear forms is expressed via non-vanishing determinant of the $n \times n$ coefficient matrix over $\mathbb{R}$ or $\mathbb{Q}_p$, and algebraicity over $\mathbb{Q}$ is stated with Mathlib's `IsAlgebraic ℚ`. Proper subspaces of $\mathbb{Q}^n$ are modeled as submodules `V : Submodule ℚ (Fin n → ℚ)` with `V ≠ ⊤`.
-- source:
--   H. P. Schlickewei, The p-adic Thue–Siegel–Roth–Schmidt theorem, Arch. Math. 29 (1977), 267–270, Theorem 1 (p. 268); W. M. Schmidt, Diophantine Approximation, Lecture Notes in Mathematics 785, Springer, 1980, Chapter VI; Y. Bugeaud, Approximation by Algebraic Numbers, Cambridge Tracts in Mathematics 160, Cambridge University Press, 2004, Chapter 2; B. Adamczewski and Y. Bugeaud, On the complexity of algebraic numbers I. Expansions in integer bases, Ann. of Math. (2) 165 (2007), 547–565, Section 3.

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace SubspaceTheorem

theorem p_adic_subspace_theorem
    (n : ℕ) (hn : 2 ≤ n)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (L_inf : Matrix (Fin n) (Fin n) ℝ)
    (hL_inf_alg : ∀ i j, IsAlgebraic ℚ (L_inf i j))
    (hL_inf_det : L_inf.det ≠ 0)
    (L_p : ∀ p : ℕ, [Fact p.Prime] → Matrix (Fin n) (Fin n) ℚ_[p])
    (hL_p_alg : ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ i j, IsAlgebraic ℚ (L_p p i j))
    (hL_p_det : ∀ (p : ℕ) [Fact p.Prime], p ∈ S → (L_p p).det ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (T : Finset (Submodule ℚ (Fin n → ℚ))),
      (∀ V ∈ T, V ≠ ⊤) ∧
      ∀ x : Fin n → ℤ, x ≠ 0 →
        (∏ i : Fin n, |L_inf.mulVec (fun j => (x j : ℝ)) i|) *
          (∏ p : {p : ℕ // p ∈ S},
            haveI : Fact p.1.Prime := ⟨hS p.1 p.2⟩
            ∏ i : Fin n, ‖(L_p p.1).mulVec (fun j => (x j : ℚ_[p.1])) i‖) <
          ((Finset.univ.sup (fun i => (x i).natAbs) : ℕ) : ℝ) ^ (-δ) →
        ∃ V ∈ T, (fun j => (x j : ℚ)) ∈ V := by sorry

end SubspaceTheorem
