-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_proposition_2_7
-- name    : ScatCaps.LinearSets.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:50.19898+00:00
-- url     : https://prove2.me/theorems/db067fd3-e88d-4946-9b1b-b97ed8072daf
-- title:
--   Proposition 2.7, p. 12 — the binomial f_{i,a,b} with f(x)/x ∉ 𝔽_{q^n} gives a scattered linear set of rank 3n
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Let $a,b\in\mathbb F_{q^{3n}}^*$, let $i$ satisfy $1\le i$, $2n+i\le3n-1$ and $\gcd(i,2n)=1$, and put
--
--   $$
--   f_{i,a,b}(x)=ax^{q^i}+bx^{q^{2n+i}}\qquad(x\in\mathbb F_{q^{3n}}).
--   $$
--
--   Let $\omega\in\mathbb F_{q^{2n}}\setminus\mathbb F_{q^n}$ with $\omega^2=A+B\omega$, $A,B\in\mathbb F_{q^n}$, $A\ne0$. If
--
--   $$
--   \frac{f_{i,a,b}(x)}{x}\notin\mathbb F_{q^n}\qquad\text{for each }x\in\mathbb F_{q^{3n}}^*,\tag{16}
--   $$
--
--   then $L_U=\{\langle f_{i,a,b}(x)+x\omega\rangle_{\mathbb F_{q^{2n}}}:x\in\mathbb F_{q^{3n}}^*\}$ is a scattered $\mathbb F_q$-linear set of rank $3n$ of $\mathrm{PG}(2,q^{2n})$.
--
--   This is the binomial criterion behind the $q=2$ family of Theorem 2.10.
--
--   **Formalization Note** $E$ is a finite field of characteristic $p$ with $|E|=q^{6n}$, and $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$. The linear set $L_U$ is represented by the $\mathbb F_q$-subspace $U$; "rank $3n$" is $|U|=q^{3n}$, and "scattered" is the weight-one condition in the form $u\in U\setminus\{0\},\ \lambda\in\mathbb F_{q^{2n}},\ \lambda u\in U\Rightarrow\lambda\in\mathbb F_q$, with points spanned over $\mathbb F_{q^{2n}}$ (not over $E$). The page prints "$f_{i,a,b}(x)+wx$" and closes the set with "⟩"; these are typos for $\omega x$ and "}", and the Lean uses $U_f$ of equation (2). The range $1\le i,\ 2n+i\le 3n-1$ is the heading of the binomial case (p. 10: $1\le i,j\le3n-1$ with $j=2n+i$).
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 12, Proposition 2.7 (and the binomial-case heading, p. 10)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem proposition_2_7 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (i : ℕ) (hi : 1 ≤ i ∧ 2 * n + i ≤ 3 * n - 1)
    (hgi : Nat.gcd i (2 * n) = 1)
    (a b : E) (ha : a ∈ subfieldOf E p h (3 * n) ∧ a ≠ 0)
    (hb : b ∈ subfieldOf E p h (3 * n) ∧ b ≠ 0)
    (ω A B : E)
    (hω : ω ∈ subfieldOf E p h (2 * n) ∧ ω ∉ subfieldOf E p h n)
    (hA : A ∈ subfieldOf E p h n) (hB : B ∈ subfieldOf E p h n)
    (hA0 : A ≠ 0) (hω2 : ω ^ 2 = A + B * ω)
    (havoid : ∀ x : E, x ∈ subfieldOf E p h (3 * n) → x ≠ 0 →
      binom q n i a b x / x ∉ subfieldOf E p h n) :
    IsFqSubspace (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) (binom q n i a b) ω) ∧
    HasRank (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) (binom q n i a b) ω) (3 * n) ∧
    IsScattered (subfieldOf E p h 1) (subfieldOf E p h (2 * n))
      (sec2Set (subfieldOf E p h (3 * n)) (binom q n i a b) ω) := by sorry

end ScatCaps.LinearSets
