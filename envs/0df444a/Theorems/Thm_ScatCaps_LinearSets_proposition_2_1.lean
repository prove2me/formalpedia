-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_proposition_2_1
-- name    : ScatCaps.LinearSets.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:06.392973+00:00
-- url     : https://prove2.me/theorems/15b43c42-2800-43fc-ad76-f942f34af7ec
-- title:
--   Proposition 2.1, p. 5 — U_f has rank 3n, and L_U is scattered iff Q_f ∩ 𝔽_{q^{2n}} = 𝔽_q
-- statement:
--   Throughout, $q=p^h$ is a prime power, $n\ge2$, and $E=\mathbb F_{q^{6n}}$. For $m\in\{1,n,2n,3n\}$, $\mathbb F_{q^m}$ denotes the unique subfield of $E$ of order $q^m$, and $\mathbb F_{q^m}^*=\mathbb F_{q^m}\setminus\{0\}$. The field $E$ is a $3$-dimensional vector space over $\mathbb F_{q^{2n}}$, and $\mathbb P=\mathrm{PG}(\mathbb F_{q^{6n}},\mathbb F_{q^{2n}})=\mathrm{PG}(2,q^{2n})$ is the associated projective plane: its points are the $\mathbb F_{q^{2n}}$-spans $\langle v\rangle_{\mathbb F_{q^{2n}}}$ of nonzero $v\in E$.
--
--   Let $f:\mathbb F_{q^{3n}}\to\mathbb F_{q^{3n}}$ be $\mathbb F_q$-linear and let $\omega\in\mathbb F_{q^{2n}}\setminus\mathbb F_{q^n}$. Put
--
--   $$
--   U=\{f(x)+x\omega : x\in\mathbb F_{q^{3n}}\},\qquad Q_f=\Big\{\frac{f(x)+x\omega}{f(y)+y\omega} : x,y\in\mathbb F_{q^{3n}},\ y\neq0\Big\}.
--   $$
--
--   Then $U$ is an $\mathbb F_q$-subspace of $E$ of rank $3n$, so $L_U=\{\langle f(x)+x\omega\rangle_{\mathbb F_{q^{2n}}}: x\in\mathbb F_{q^{3n}}^*\}$ is an $\mathbb F_q$-linear set of rank $3n$ of $\mathrm{PG}(2,q^{2n})$, and
--
--   $$
--   L_U\ \text{is scattered}\iff Q_f\cap\mathbb F_{q^{2n}}=\mathbb F_q .
--   $$
--
--   This is the basic criterion behind all constructions of §2.
--
--   **Formalization Note** $E$ is a finite field of characteristic $p$ with $|E|=q^{6n}$, and $\mathbb F_{q^m}$ is the fixed field of $x\mapsto x^{q^m}$. The linear set $L_U$ is represented by the $\mathbb F_q$-subspace $U$; "rank $3n$" is $|U|=q^{3n}$, and "scattered" is the weight-one condition in the form $u\in U\setminus\{0\},\ \lambda\in\mathbb F_{q^{2n}},\ \lambda u\in U\Rightarrow\lambda\in\mathbb F_q$, with points spanned over $\mathbb F_{q^{2n}}$ (not over $E$). The denominators in $Q_f$ are nonzero for $y\ne0$, because $\{1,\omega\}$ is an $\mathbb F_{q^{3n}}$-basis of $E$.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 5, Proposition 2.1

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem proposition_2_1 (E : Type*) [Field E] [Fintype E]
    (p h q n : ℕ) [ExpChar E p] (hs : Section2Setting E p h q n)
    (f : E → E)
    (hf : IsLinearOn (subfieldOf E p h 1) (subfieldOf E p h (3 * n)) f)
    (ω : E) (hω : ω ∈ subfieldOf E p h (2 * n) ∧ ω ∉ subfieldOf E p h n) :
    IsFqSubspace (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) f ω) ∧
    HasRank (subfieldOf E p h 1)
      (sec2Set (subfieldOf E p h (3 * n)) f ω) (3 * n) ∧
    (IsScattered (subfieldOf E p h 1) (subfieldOf E p h (2 * n))
        (sec2Set (subfieldOf E p h (3 * n)) f ω) ↔
      quotientSet (subfieldOf E p h (3 * n)) f ω ∩
          (subfieldOf E p h (2 * n) : Set E) =
        (subfieldOf E p h 1 : Set E)) := by sorry

end ScatCaps.LinearSets
