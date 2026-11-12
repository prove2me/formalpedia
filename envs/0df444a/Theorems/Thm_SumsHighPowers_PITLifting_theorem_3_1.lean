-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_theorem_3_1
-- name    : SumsHighPowers.PITLifting.theorem_3_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T16:10:45.929199+00:00
-- url     : https://prove2.me/theorems/535c218d-41c0-4ff8-8c83-60c4007de961
-- title:
--   Theorem 3.1 — a nonzero sum of $r$ high powers from $C_\Delta$ vanishes at most $(s-1)\Delta d$ times on the curve through a hitting set of $\Sigma^2C_\Delta$
-- statement:
--   Let $F$ be a field and $C\subseteq F[x_1,\dots,x_n]$ a class of polynomials. For $\Delta\in\mathbb N$ let $C_\Delta$ be the members of $C$ of total degree at most $\Delta$, and for $r,d\in\mathbb N$ let
--   $$\Sigma^r\wedge^d C_\Delta=\Big\{\sum_{i=1}^r\alpha_i f_i^{\,d}:\alpha_i\in F,\ f_i\in C_\Delta\Big\},\qquad \Sigma^2C_\Delta=\Sigma^2\wedge^1C_\Delta .$$
--   Let $r,d,\Delta\in\mathbb N$ with $d+1\ge(r-1)^2$. Assume $u_1,\dots,u_s\in F^n$ is a **hitting set** for $\Sigma^2C_\Delta$ (every nonzero member of $\Sigma^2C_\Delta$ is nonzero at some $u_i$) and that $F$ has characteristic $p=0$ or $p>(r-1)d\Delta s$. Choose pairwise distinct $a_1,\dots,a_s\in F$ and let $H(t)=(H_1(t),\dots,H_n(t))$ be the unique polynomial map with $\deg H_j\le s-1$ and $H(a_i)=u_i$ for every $i\in[s]$. Then for every $S\subseteq F$ and every nonzero $P\in\Sigma^r\wedge^dC_\Delta$,
--   $$\#\{a\in S:\ P(H(a))=0\}\ \le\ (s-1)\cdot\Delta\cdot d .$$
--   The points are counted with their parameters (footnote 6): if $H(a)=H(b)$ for $a\neq b$ in $S$, both are counted.
--
--   Taking $S$ to be any set of $(s-1)\Delta d+1$ elements of $F$ gives a hitting set for $\Sigma^r\wedge^dC_\Delta$ of that size from one for $\Sigma^2C_\Delta$: PIT for sums of high powers reduces to PIT for sums of two members of the inner class. This is the formal version of Theorem 1.1(i), and the explicit hitting sets of §§4–7 are obtained from it.
--
--   **Formalization Note.** The curve is any `H : Fin n → F[X]` with `(H j).degree < s` interpolating the points (unique by Lagrange interpolation); the count is `Set.encard`, so an infinite set of zeros would count as $\infty$; $s-1$ and $r-1$ are natural-number subtraction.
--
--   Differences from the source:
--   - generalization: C is a polynomial class closed under scalar multiplications → `C` is an arbitrary set of polynomials (no closure hypothesis); reason: Σ²C_Δ is defined with scalars (p. 4), so α·g ∈ Σ²C_Δ for every g ∈ C_Δ without any hypothesis on C, which is the only use of the closure in the proof; a class closed under scalar multiplications is an instance
--   - generalization: a hitting set H = {u_1, …, u_s} for Σ²C_Δ of size s (a set, ordered arbitrarily) → a family `u : Fin s → (Fin n → F)` with `IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u`, repetitions allowed; reason: an injective family is exactly the paper's ordered set of size s; the statement is proved for every family
--   - encoding: H(t) the unique polynomial map whose coordinates have degree at most s − 1 and H(a_i) = u_i, with a_1, …, a_s pairwise distinct → any `H : Fin n → F[X]` with `(H j).degree < s` and `(H j).eval (a i) = u i j` for all i, j, and `a` injective; reason: by Lagrange interpolation such an H exists and is unique, so the hypotheses pin down the paper's curve; for s = 0 they force H = 0
--   - encoding: a class C ⊆ F[x_1, …, x_n]; C_Δ (total degree ≤ Δ); Σ^r ∧^d C_Δ and Σ²C_Δ (p. 4, p. 12) → `C : Set (MvPolynomial (Fin n) F)`, `degBounded C Δ` (totalDegree ≤ Δ), `sumPowClass r d (degBounded C Δ)` and `sumPowClass 2 1 (degBounded C Δ)`; reason: the paper's definitions, with variables indexed by Fin n and summands by Fin r
--   - encoding: P vanishes on at most N points from the ordered set H(S) (footnote 6: parameters counted separately) → `{t | t ∈ S ∧ MvPolynomial.eval (fun j => (H j).eval t) P = 0}.encard ≤ ((s - 1) * Δ * d : ℕ)`; reason: footnote 6 counts parameters t ∈ S, not image points; `Set.encard` is the cardinality in ℕ∞, so an infinite zero set is not counted as 0
--   - encoding: (r − 1) and (s − 1) in d + 1 ≥ (r − 1)², (r − 1)dΔs and (s − 1)·Δ·d → natural-number subtraction; reason: for r = 0, Σ^0 ∧^d C_Δ = {0} so no nonzero P exists; for s = 0 the hitting-set hypothesis forces C_Δ ⊆ {0}, so a nonzero P is a nonzero constant (d = 0) with no zeros, and the bound 0 agrees with the paper's −Δ·0 = 0; for d > 0 no nonzero P exists
--   - encoding: F of characteristic p with p = 0 or p > (r − 1)dΔs → `ringChar F = 0 ∨ (r - 1) * d * Δ * s < ringChar F`; reason: the characteristic of a field is 0 or a prime p, and `ringChar F` is that number
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 29, Theorem 3.1 (Black-box PIT for High Powers, formal version of Theorem 1.1(i)); proof p. 30

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_SumPowClass
import Definitions.Def_SumsHighPowers_PITLifting_IsHittingSet

namespace SumsHighPowers.PITLifting

/-- **Theorem 3.1** (Black-box PIT for High Powers, formal version of Theorem 1.1(i);
Kaplan–Shpilka–Tal, p. 29). Let `r, d, Δ ∈ ℕ` with `d + 1 ≥ (r − 1)²`, let `C` be a polynomial
class, let `u₁, …, u_s` be a hitting set for `Σ²C_Δ`, and let `F` have characteristic `p = 0` or
`p > (r − 1)dΔs`. Choose pairwise distinct `a₁, …, a_s ∈ F` and let `H(t)` be the polynomial map
whose coordinates have degree at most `s − 1` with `H(aᵢ) = uᵢ`. Then for any `S ⊆ F`, any nonzero
`P ∈ Σ^r ∧^d C_Δ` vanishes at `H(a)` for at most `(s − 1)·Δ·d` parameters `a ∈ S` (footnote 6:
parameters are counted, not image points). -/
theorem theorem_3_1 {F : Type*} [Field F] (n r d Δ s : ℕ)
    (hrd : (r - 1) ^ 2 ≤ d + 1)
    (C : Set (MvPolynomial (Fin n) F))
    (u : Fin s → Fin n → F) (hu : IsHittingSet (sumPowClass 2 1 (degBounded C Δ)) u)
    (hchar : ringChar F = 0 ∨ (r - 1) * d * Δ * s < ringChar F)
    (a : Fin s → F) (ha : Function.Injective a)
    (H : Fin n → Polynomial F) (hHdeg : ∀ j, (H j).degree < s)
    (hHint : ∀ i j, (H j).eval (a i) = u i j)
    (S : Set F) (P : MvPolynomial (Fin n) F)
    (hP : P ∈ sumPowClass r d (degBounded C Δ)) (hP0 : P ≠ 0) :
    {t | t ∈ S ∧ MvPolynomial.eval (fun j => (H j).eval t) P = 0}.encard ≤
      (((s - 1) * Δ * d : ℕ) : ℕ∞) := by sorry

end SumsHighPowers.PITLifting
