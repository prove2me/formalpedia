-- Prove2me | Theorems.Thm_TrDegJac_Supplement_theorem_3_41
-- name    : TrDegJac.Supplement.theorem_3_41
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:33:11.241194+00:00
-- url     : https://prove2.me/theorems/ae07a787-5bf1-4cd1-9882-aa63713709b5
-- title:
--   Theorem 3.41 — over every field, a non-zero polynomial of degree $O(n^2)$ vanishes on all non-$(\epsilon n,\epsilon n^2)$-rigid $n\times n$ matrices (corrected: $n\ge1$)
-- statement:
--   Let $\mathbb F[x_{1,1},\dots,x_{n,n}]$ be the polynomial ring in the $n^2$ entries of an $n\times n$ matrix, and for a polynomial $A$ and a matrix $M\in\mathbb F^{n\times n}$ write $A(M)$ for the value of $A$ at the entries of $M$. Call $M$ **not $(r,s)$-rigid** if $M=L+S$ with $\operatorname{rank}L\le r$ and $S$ having at most $s$ non-zero entries.
--
--   There is an absolute constant $C$ such that the following holds. For every field $\mathbb F$, every real $\epsilon<1/8$ and every $n\ge 1$ there is a non-zero polynomial $A\in\mathbb F[x_{1,1},\dots,x_{n,n}]$ with
--   $$
--   \deg A\le C\,n^2\qquad\text{and}\qquad A(M)=0\ \text{ for every } M\in\mathbb F^{n\times n}\text{ that is not }(\epsilon n,\epsilon n^2)\text{-rigid}.
--   $$
--   Here $\deg$ is the total degree.
--
--   So $A$ is a non-trivial equation for the set of non-rigid matrices: every matrix at which $A$ does not vanish is $(\epsilon n,\epsilon n^2)$-rigid. Compared with the Kumar–Volk bound (degree $n^3$, for $\epsilon<1/25$ and fields of size at least $n^2$), the degree is $O(n^2)$ and there is no restriction on the field.
--
--   **Formalization Note** The polynomial ring is `MvPolynomial (Fin n × Fin n) F`, with the variable $(i,j)$ standing for $x_{i+1,j+1}$, and $A(M)$ is `MvPolynomial.eval` at $(i,j)\mapsto M_{ij}$. Non-rigidity is `TrDegJac.Supplement.IsNonRigid (ε * n) (ε * n ^ 2) M`. The $O(n^2)$ is a natural number $C$ quantified before the field, $\epsilon$ and $n$. The field is an arbitrary `Field` in a fixed universe.
--
--   Differences from the source:
--   - correction: "for every n" → $n\ge 1$; reason: at $n=0$ the statement is false for every $\epsilon$: the empty matrix is $0+0$ with rank $0\le\epsilon\cdot 0=0$ and $0\le\epsilon\cdot 0^2=0$ non-zero entries, so it is non-rigid, while a non-zero polynomial in no variables is a non-zero constant and does not vanish there.
--   - reading: degree at most $O(n^2)$, for the given $\epsilon$ → one constant $C\in\mathbb N$, chosen before $\mathbb F$, $\epsilon$ and $n$, with total degree $\le C n^2$; reason: the page does not say whether the constant hidden in $O(n^2)$ may depend on $\epsilon$ or $\mathbb F$; the stronger, uniform reading is taken, and the proof supplies it (Corollary 3.40 with $\le 2^{n^2}$ maps, $< 3n^2/8$ parameters, degree $2$ gives degree $\le 2^{11/5}n^2$ uniformly in $\mathbb F$, $\epsilon$, $n$); for each fixed $\epsilon$ it implies the per-$\epsilon$ reading.
--   - encoding: $F[x_{1,1},\dots,x_{n,n}]$, $A(M)$ → `MvPolynomial (Fin n × Fin n) F`, evaluation at the entries of $M$; reason: a relabelling of the variables; the same polynomials.
--   - encoding: every field $\mathbb F$ → every `Field F` with `F : Type u`, the statement universe-polymorphic in `u`; reason: Lean cannot quantify over universes inside a proposition; every field lies in some universe, so every instance of the source is covered.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42c5143c0b6b5eb0d6c9e7be9b837e30a44865fdefd2ea6a908192e92b), Theorem 3.41, p.25 (non-rigidity defined §1.2, p.5 and §3.3, p.22)

import Mathlib
import Definitions.Def_TrDegJac_Supplement_IsNonRigid

set_option autoImplicit false

universe u

namespace TrDegJac.Supplement

/-- **Theorem 3.41 (a degree-O(n²) equation for non-rigid matrices over every field)** — Forbes and
Staicu, *Approximating Transcendence Degree in Medium Characteristic*, STOC 2027 submission
(manuscript sha256 3ab72a42…), p.25:
"Let ϵ < 1/8 and F be any field. For every n, there exists a non-zero polynomial
A ∈ F[x₁,₁, …, x_{n,n}] of degree at most O(n²), which is a non-trivial equation for matrices that
are not (ϵn, ϵn²)-rigid. That is, for every such matrix M, A(M) = 0."

**Formalization Note.** `O(n²)` is one natural-number constant `C`, chosen before the field `F`,
`ε` and `n`, with `totalDegree A ≤ C · n²`. `F[x₁,₁, …, x_{n,n}]` is
`MvPolynomial (Fin n × Fin n) F` (the variable `(i, j)` is the entry `x_{i+1, j+1}`), and `A(M)` is
evaluation at the entries of `M`. "Not (ϵn, ϵn²)-rigid" is `IsNonRigid (ε * n) (ε * n ^ 2) M`
over the same field `F`. The field is arbitrary (finite fields included); `ε` is any real number
below `1/8`, as printed. `n ≥ 1` corrects the printed "for every n": at `n = 0` the empty matrix is
non-rigid (for `ε ≥ 0`) and a non-zero polynomial in no variables is a non-zero constant, which
does not vanish there. -/
theorem theorem_3_41 :
    ∃ C : ℕ, ∀ (F : Type u) [Field F] (ε : ℝ), ε < 1 / 8 → ∀ n : ℕ, 1 ≤ n →
      ∃ A : MvPolynomial (Fin n × Fin n) F, A ≠ 0 ∧ A.totalDegree ≤ C * n ^ 2 ∧
        ∀ M : Matrix (Fin n) (Fin n) F, IsNonRigid (ε * n) (ε * n ^ 2) M →
          MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2) A = 0 := by sorry

end TrDegJac.Supplement
