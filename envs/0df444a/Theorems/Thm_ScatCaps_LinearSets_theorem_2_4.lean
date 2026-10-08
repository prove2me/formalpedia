-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_theorem_2_4
-- name    : ScatCaps.LinearSets.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:56.126072+00:00
-- url     : https://prove2.me/theorems/83252a2d-4812-4d2f-8628-37c7e5480e0c
-- title:
--   Theorem 2.4, p. 9 — L_U for f(x) = a x^{q^i} is scattered of rank 3n when q ≡ 1 mod 3
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Assume $q\equiv1\pmod 3$. Let $a\in\mathbb F_{q^{3n}}^*$ and $1\le i\le 3n-1$ satisfy
--
--   1. $\gcd(i,2n)=\gcd(i,3n)=1$;
--   2. $\big(N_{q^{3n}/q}(a)\big)^{(q-1)/3}\neq1$, where $N_{q^{3n}/q}(a)=\prod_{j=0}^{3n-1}a^{q^j}$.
--
--   Then for every $\omega\in\mathbb F_{q^{2n}}\setminus\mathbb F_{q^n}$ the set
--
--   $$
--   L_U=\{\langle ax^{q^i}+x\omega\rangle_{\mathbb F_{q^{2n}}} : x\in\mathbb F_{q^{3n}}^*\}
--   $$
--
--   is a scattered $\mathbb F_q$-linear set of $\mathrm{PG}(2,q^{2n})$ of rank $3n$.
--
--   Condition 2 says that $N_{q^{3n}/q}(a)$ is not a cube in $\mathbb F_q^*$. This family covers Theorem 1.2 when $q\equiv1\pmod3$ and $3\mid t$.
--
--   **Formalization Note** $E$ is a finite field of characteristic $p$ with $|E|=q^{6n}$, and $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$. The linear set $L_U$ is represented by the $\mathbb F_q$-subspace $U$; "rank $3n$" is $|U|=q^{3n}$, and "scattered" is the weight-one condition in the form $u\in U\setminus\{0\},\ \lambda\in\mathbb F_{q^{2n}},\ \lambda u\in U\Rightarrow\lambda\in\mathbb F_q$, with points spanned over $\mathbb F_{q^{2n}}$ (not over $E$). The exponent $(q-1)/3$ is natural-number division, exact because $q\equiv1\pmod3$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 9, Theorem 2.4 (and the monomial-case heading, p. 7)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem theorem_2_4 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (hq3 : q % 3 = 1) (i : ℕ) (hi : 1 ≤ i ∧ i ≤ 3 * n - 1)
    (hgi : Nat.gcd i (2 * n) = 1 ∧ Nat.gcd i (3 * n) = 1)
    (a : E) (ha : a ∈ subfieldOf E p h (3 * n) ∧ a ≠ 0)
    (hNa : (relNorm q (3 * n) 1 a) ^ ((q - 1) / 3) ≠ 1)
    (ω : E) (hω : ω ∈ subfieldOf E p h (2 * n) ∧ ω ∉ subfieldOf E p h n) :
    IsFqSubspace (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) (monom q i a) ω) ∧
    HasRank (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) (monom q i a) ω) (3 * n) ∧
    IsScattered (subfieldOf E p h 1) (subfieldOf E p h (2 * n))
      (sec2Set (subfieldOf E p h (3 * n)) (monom q i a) ω) := by sorry

end ScatCaps.LinearSets
