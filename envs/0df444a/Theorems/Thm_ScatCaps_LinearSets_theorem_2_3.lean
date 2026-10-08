-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_theorem_2_3
-- name    : ScatCaps.LinearSets.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:56.851141+00:00
-- url     : https://prove2.me/theorems/c6397f7a-e5a1-4e7a-a6de-e683b8b47720
-- title:
--   Theorem 2.3, p. 7 — L_U for f(x) = a x^{q^i} is scattered of rank 3n when n ≢ 0 mod 3
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Assume $n\not\equiv0\pmod 3$. Let $a\in\mathbb F_{q^{3n}}^*$ and $1\le i\le 3n-1$ satisfy
--
--   1. $\gcd(i,2n)=1$ and $\gcd(i,3n)=3$;
--   2. $N_{q^{3n}/q^3}(a)\notin\mathbb F_q$, where $N_{q^{3n}/q^3}(a)=\prod_{j=0}^{n-1}a^{q^{3j}}$.
--
--   Then for every $\omega\in\mathbb F_{q^{2n}}\setminus\mathbb F_{q^n}$ the set
--
--   $$
--   L_U=\{\langle ax^{q^i}+x\omega\rangle_{\mathbb F_{q^{2n}}} : x\in\mathbb F_{q^{3n}}^*\}
--   $$
--
--   is a scattered $\mathbb F_q$-linear set of $\mathrm{PG}(2,q^{2n})$ of rank $3n$.
--
--   This is the first of the paper's three plane families, used for Theorem 1.2 when $t\not\equiv0\pmod3$.
--
--   **Formalization Note** $E$ is a finite field of characteristic $p$ with $|E|=q^{6n}$, and $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$. The linear set $L_U$ is represented by the $\mathbb F_q$-subspace $U$; "rank $3n$" is $|U|=q^{3n}$, and "scattered" is the weight-one condition in the form $u\in U\setminus\{0\},\ \lambda\in\mathbb F_{q^{2n}},\ \lambda u\in U\Rightarrow\lambda\in\mathbb F_q$, with points spanned over $\mathbb F_{q^{2n}}$ (not over $E$). The range $1\le i\le3n-1$ and $a\ne0$ come from the heading of the monomial case (p. 7). The page fixes one $\omega$ at the start of §2; the statement holds for every such $\omega$ and is quantified that way.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 7, Theorem 2.3 (and the monomial-case heading, p. 7)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem theorem_2_3 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (hn3 : n % 3 ≠ 0) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ 3 * n - 1)
    (hgi : Nat.gcd i (2 * n) = 1 ∧ Nat.gcd i (3 * n) = 3)
    (a : E) (ha : a ∈ subfieldOf E p h (3 * n) ∧ a ≠ 0)
    (hNa : relNorm q (3 * n) 3 a ∉ subfieldOf E p h 1)
    (ω : E) (hω : ω ∈ subfieldOf E p h (2 * n) ∧ ω ∉ subfieldOf E p h n) :
    IsFqSubspace (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) (monom q i a) ω) ∧
    HasRank (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) (monom q i a) ω) (3 * n) ∧
    IsScattered (subfieldOf E p h 1) (subfieldOf E p h (2 * n))
      (sec2Set (subfieldOf E p h (3 * n)) (monom q i a) ω) := by sorry

end ScatCaps.LinearSets
