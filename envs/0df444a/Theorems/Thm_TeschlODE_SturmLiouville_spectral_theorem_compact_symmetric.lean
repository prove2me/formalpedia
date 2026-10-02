-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_spectral_theorem_compact_symmetric
-- name    : TeschlODE.SturmLiouville.spectral_theorem_compact_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:26:00.995527+00:00
-- url     : https://prove2.me/theorems/70c66cf6-e3cc-4852-8f46-3c6b22e0a890
-- title:
--   Theorem 5.6 — spectral theorem for compact symmetric operators on an inner product space
-- statement:
--   Let $H_0$ be a complex inner product space (not necessarily complete) and $A : H_0 \to H_0$ a compact symmetric operator. Then there are $N \in \mathbb{N}_0 \cup \{\infty\}$, real numbers $\alpha_j$ and vectors $u_j$ ($0 \le j < N$) such that
--
--   - $A u_j = \alpha_j u_j$ and $\{u_j\}_{j<N}$ is an orthonormal set (normalized eigenvectors);
--   - $N = \infty$ if $H_0$ is infinite dimensional, and $N = \dim H_0$ otherwise;
--   - if $N = \infty$ then $\alpha_j \to 0$;
--   - every $f \in \operatorname{Ran}(A) = \{Ag \mid g \in H_0\}$ can be written as
--   $$f = \sum_{j < N} \langle u_j, f\rangle u_j , \qquad (5.42)$$
--   the partial sums converging to $f$ in $H_0$;
--   - if $\operatorname{Ran}(A)$ is dense, the $u_j$ form an orthonormal basis: the expansion (5.42) holds for every $f \in H_0$ (the book's (5.34)).
--
--   **Formalization Note.** The book writes $\sum_{j=0}^{N}$ with $N \in \mathbb{N}_0 \cup \{\infty\}$ and proves the theorem assuming $H_0$ infinite dimensional "without loss of generality", where its construction produces an infinite sequence; in finite dimension the construction stops after $\dim H_0$ steps. The statement makes this explicit with `N : ℕ∞` counting the eigenvectors (indices $j < N$) and the two clauses on $N$. The series is the limit of $\sum_{j<n,\ j<N}$ as $n \to \infty$ in the norm of $H_0$. "Orthonormal basis" is the book's (5.32)/(5.34), not Mathlib's `HilbertBasis`, which needs completeness.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 151, Theorem 5.6

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsCompactOp

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.6 (spectral theorem for compact symmetric operators), p. 151: let `H₀` be
a complex inner product space and `A : H₀ → H₀` compact and symmetric. There are `N ∈ ℕ₀ ∪ {∞}`,
real eigenvalues `αⱼ` and normalized eigenvectors `uⱼ` (`j < N`) forming an orthonormal set,
with `N = ∞` when `H₀` is infinite dimensional (and `N = dim H₀` otherwise) and `αⱼ → 0` when
`N = ∞`, such that every `f ∈ Ran(A)` satisfies `f = Σ_{j<N} ⟨uⱼ, f⟩ uⱼ` (5.42), the partial sums
converging in `H₀`; if `Ran(A)` is dense, the `uⱼ` form an orthonormal basis, i.e. the same
expansion holds for every `f ∈ H₀` (5.34). -/
theorem spectral_theorem_compact_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) (hsym : A.IsSymmetric) :
    ∃ (N : ℕ∞) (α : ℕ → ℝ) (u : ℕ → E),
      (FiniteDimensional ℂ E → N = (Module.finrank ℂ E : ℕ∞)) ∧
      (¬ FiniteDimensional ℂ E → N = ⊤) ∧
      (∀ j : ℕ, (j : ℕ∞) < N → A (u j) = (α j : ℂ) • u j) ∧
      Orthonormal ℂ (fun j : {j : ℕ // (j : ℕ∞) < N} => u j) ∧
      (N = ⊤ → Filter.Tendsto α Filter.atTop (nhds 0)) ∧
      (∀ f ∈ LinearMap.range A,
        Filter.Tendsto
          (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < N),
            inner ℂ (u j) f • u j) Filter.atTop (nhds f)) ∧
      (Dense (LinearMap.range A : Set E) → ∀ f : E,
        Filter.Tendsto
          (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < N),
            inner ℂ (u j) f • u j) Filter.atTop (nhds f)) := by sorry

end TeschlODE.SturmLiouville
