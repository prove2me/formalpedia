-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_proposition_2_2
-- name    : ScatCaps.LinearSets.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:48.692718+00:00
-- url     : https://prove2.me/theorems/fb6bb8e4-ab6b-49a6-8a92-e90dcc54a3cb
-- title:
--   Proposition 2.2, p. 6 — scatteredness of L_U through equations (5) and (6)
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Let $f:\mathbb F_{q^{3n}}\to\mathbb F_{q^{3n}}$ be $\mathbb F_q$-linear and let $\omega\in\mathbb F_{q^{2n}}\setminus\mathbb F_{q^n}$ satisfy $\omega^2=A+B\omega$ with $A,B\in\mathbb F_{q^n}$, $A\neq0$. Let $U=\{f(x)+x\omega:x\in\mathbb F_{q^{3n}}\}$. Then $U$ is an $\mathbb F_q$-subspace of rank $3n$, and $L_U$ is scattered if and only if, for every pair $(x,y)\in\mathbb F_{q^{3n}}^*\times\mathbb F_{q^{3n}}^*$ satisfying
--
--   $$
--   \begin{aligned}
--   f(x)^{q^{2n}}f(y)-f(y)^{q^{2n}}f(x)&=(xy^{q^{2n}}-yx^{q^{2n}})A, &&(5)\\
--   f(x)^{q^{2n}}y+f(y)x^{q^{2n}}-f(y)^{q^{2n}}x-f(x)y^{q^{2n}}&=(xy^{q^{2n}}-yx^{q^{2n}})B, &&(6)
--   \end{aligned}
--   $$
--
--   the quotient $\lambda=\dfrac{f(x)+x\omega}{f(y)+y\omega}$ of (7) lies in $\mathbb F_q^*$.
--
--   This reformulation turns scatteredness into a polynomial system and is the entry point of the proofs of Theorems 2.3, 2.4 and Proposition 2.7.
--
--   **Formalization Note** $E$ is a finite field of characteristic $p$ with $|E|=q^{6n}$, and $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$. The linear set $L_U$ is represented by the $\mathbb F_q$-subspace $U$; "rank $3n$" is $|U|=q^{3n}$, and "scattered" is the weight-one condition in the form $u\in U\setminus\{0\},\ \lambda\in\mathbb F_{q^{2n}},\ \lambda u\in U\Rightarrow\lambda\in\mathbb F_q$, with points spanned over $\mathbb F_{q^{2n}}$ (not over $E$). The page states "$L_U$ is a scattered $\mathbb F_q$-linear set of rank $3n$ if and only if (5)–(6) ⇒ (7)"; since the rank-$3n$ part holds unconditionally (Proposition 2.1), the Lean asserts it unconditionally and puts the equivalence on scatteredness, which implies the printed form.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 6, Proposition 2.2, equations (5)–(7)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem proposition_2_2 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (f : E → E)
    (hf : IsLinearOn (subfieldOf E p h 1) (subfieldOf E p h (3 * n)) f)
    (ω A B : E)
    (hω : ω ∈ subfieldOf E p h (2 * n) ∧ ω ∉ subfieldOf E p h n)
    (hA : A ∈ subfieldOf E p h n) (hB : B ∈ subfieldOf E p h n)
    (hA0 : A ≠ 0) (hω2 : ω ^ 2 = A + B * ω) :
    IsFqSubspace (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) f ω) ∧
    HasRank (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) f ω) (3 * n) ∧
    (IsScattered (subfieldOf E p h 1) (subfieldOf E p h (2 * n))
      (sec2Set (subfieldOf E p h (3 * n)) f ω) ↔
      ∀ x y : E, x ∈ subfieldOf E p h (3 * n) →
        y ∈ subfieldOf E p h (3 * n) → x ≠ 0 → y ≠ 0 →
        (f x) ^ (q ^ (2 * n)) * f y - (f y) ^ (q ^ (2 * n)) * f x =
          (x * y ^ (q ^ (2 * n)) - y * x ^ (q ^ (2 * n))) * A →
        (f x) ^ (q ^ (2 * n)) * y + f y * x ^ (q ^ (2 * n)) -
          (f y) ^ (q ^ (2 * n)) * x - f x * y ^ (q ^ (2 * n)) =
          (x * y ^ (q ^ (2 * n)) - y * x ^ (q ^ (2 * n))) * B →
        (f x + x * ω) / (f y + y * ω) ∈ subfieldOf E p h 1 ∧
          (f x + x * ω) / (f y + y * ω) ≠ 0) := by sorry

end ScatCaps.LinearSets
