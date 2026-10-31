-- Prove2me | Theorems.Thm_ParriloTheta_theorem_2_1
-- name    : ParriloTheta.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:21.74478+00:00
-- url     : https://prove2.me/theorems/977a0380-7b52-467f-b71e-c55c7c0caeeb
-- title:
--   Theorem 2.1 (Peña, Vera, Zuluaga) — $q(x^{\circ2})\in\Sigma$ iff $q=\sum_I\sigma_I\prod_{i\in I}x_i$
-- statement:
--   Let $q\in\mathbb R[x_1,\dots,x_n]$ be homogeneous of degree $d$ and let $Q(x)=q(x_1^2,\dots,x_n^2)$, of degree $2d$. Then $Q$ is a sum of squares if and only if
--   $$
--   q(x)=\sum_{\substack{I\subseteq[n]\\ |I|\le d,\ |I|\equiv d\ (\mathrm{mod}\ 2)}}\sigma_I(x)\prod_{i\in I}x_i ,
--   $$
--   where each $\sigma_I$ is a homogeneous polynomial of degree $d-|I|$ which is a sum of squares.
--
--   The paper cites this result and uses it to describe the cones $\mathcal K^{(0)}$ and $\mathcal K^{(1)}$ by coefficient comparison.
--
--   **Formalization Note** $Q$ is `aeval (fun i => X i ^ 2) q`; the family $\sigma$ is indexed by all subsets $I$, and only those with $|I|\le d$ and $|I|\equiv d \pmod 2$ are constrained and appear in the sum.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n indexed by [n] → variables indexed by a finite type ι with decidable equality; reason: Lean convention; same polynomials up to relabelling
--   - encoding: one σ_I for each admissible I → σ : Finset ι → MvPolynomial ι ℝ, constrained only on admissible I; reason: values at other I are unused; same decompositions
-- source:
--   Laurent & Vargas, Exactness of Parrilo's conic approximations for copositive matrices and associated low order bounds for the stability number of a graph, arXiv:2109.12876v1, Theorem 2.1, p.5 (cited from Peña, Vera and Zuluaga [31])

import Mathlib

open MvPolynomial

namespace ParriloTheta

/-- **Theorem 2.1 (Peña, Vera and Zuluaga [31]).**
Laurent & Vargas, *Exactness of Parrilo's conic approximations for copositive matrices and
associated low order bounds for the stability number of a graph*, arXiv:2109.12876v1, Theorem 2.1, p.5:
"Let q ∈ R[x] be a homogeneous polynomial of degree d and define the degree 2d polynomial
Q(x) := q(x∘2) = q(x_1^2, . . . , x_n^2). Then, Q ∈ Σ if and only if q can be decomposed as
q(x) = ∑_{I⊆[n], |I|≤d, |I|≡d (mod 2)} σ_I(x) ∏_{i∈I} x_i, (2.1)
where σ_I is a homogeneous polynomial with degree d − |I| and σ_I ∈ Σ."

**Formalization Note.** The variables are indexed by a finite type `ι` (the paper's `[n]`).
`q(x∘2)` is `aeval (fun i => X i ^ 2) q`. The family `σ` is indexed by all finsets `I` of
`ι`; only the `I` with `|I| ≤ d` and `|I| ≡ d (mod 2)` enter the sum and are constrained. -/
theorem theorem_2_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (q : MvPolynomial ι ℝ) (d : ℕ)
    (hq : q.IsHomogeneous d) :
    IsSumSq (aeval (fun i => (X i : MvPolynomial ι ℝ) ^ 2) q) ↔
      ∃ σ : Finset ι → MvPolynomial ι ℝ,
        (∀ I : Finset ι, I.card ≤ d → I.card % 2 = d % 2 →
          (σ I).IsHomogeneous (d - I.card) ∧ IsSumSq (σ I)) ∧
        q = ∑ I ∈ Finset.univ.filter (fun I : Finset ι => I.card ≤ d ∧ I.card % 2 = d % 2),
              σ I * ∏ i ∈ I, X i := by sorry

end ParriloTheta
