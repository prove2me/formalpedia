-- Prove2me | Theorems.Thm_QuantumSixJ_Network_rung_eigenvalue
-- name    : QuantumSixJ.Network.rung_eigenvalue
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:44:14.74421+00:00
-- url     : https://prove2.me/theorems/9a356ef2-a0e4-4303-be22-daa952f214d9
-- title:
--   Eqs. (12)–(15) — rung eigenvalue identity
-- statement:
--   Let $\mathcal C$ be a $K$-linear preadditive monoidal category, $K=\mathbb C(q)$, with additive and $K$-linear tensor product. The chosen objects $V_n$ for natural labels satisfy $V_0\cong\mathbb1$ and have exact self-pairings. Assume `SuQ2Axioms`: unique scalar endomorphisms of each $V_n$, zero morphisms between different labels, the admissible $\mathrm{SL}(2)$ fusion decompositions, and the loop values $\Delta_n$. Choose trivalent vertices $W$, and assume `VertexNormalized W`: theta normalization and cyclicity. Scalars act through $\iota:\mathbb Q(q)\hookrightarrow K$, fixing $q$. Composition $f;g$ means first $f$, then $g$.
--
--   Also assume the separate initial data `TetSeed W`: for every natural $a,b,c,d,j$, $T(a,b,c,d;j,2)=\iota(\operatorname{Tet}^{\mathrm{sum}}(a,b,c,d;j,2))\,\mathrm{id}_{\mathbb1}$. These are seed values, not an all-channel network-to-sum identity.
--
--   For `K2`, the rung operator weighted by $[a][b]$, and `Kop`, its extension to the first two of four legs, prove three identities for all natural labels:
--   1. Closing the triangle gives exactly
--   $$\eta_l;((\operatorname{split}_{l;ab};K2_{ab};\operatorname{fuse}_{ab;l})\otimes\mathrm{id}_{V_l});\epsilon_l
--   =\iota([a][b])\,T(a,a,b,b;l,2).$$
--   The cup/cap and strand order are those of the specified exact self-pairing.
--   2. $\operatorname{split}_{l;ab};K2_{ab}=\iota(\Lambda(a,b,l))\operatorname{split}_{l;ab}$.
--   3. $X(a,b,c,d;l);\mathrm{Kop}_{abcd}=\iota(\Lambda(a,b,l))X(a,b,c,d;l)$.
--
--   No admissibility restriction is imposed: invalid-channel cases must follow from the category and zero conventions. Neither a triangle evaluation nor an eigenvector equation is added as a hypothesis.
--
--   ### Independent mathematical read-back
--
--   # Rung closure and eigenvalue identities
--
--   ## Setting and hypotheses
--
--   Let \(F=\mathbb Q(q)\), \(K=\mathbb C(q)\), and let \(\iota:F\to K\) be the coefficient embedding fixing the indeterminate \(q\). Work in an arbitrary category \(\mathcal C\), with arbitrary object and morphism universes, that is preadditive and \(K\)-linear, monoidal, monoidally preadditive, and monoidally \(K\)-linear. Thus composition and tensoring respect the indicated additive and scalar structures. No braiding, symmetry, dagger, positivity, or concrete representation realization is specified.
--
--   The label data consist of objects \(V_n\) for every natural number \(n\), an isomorphism \(V_0\cong\mathbf1\), and a chosen exact self-pairing on every \(V_n\). Write its cup and cap as \(D_n:\mathbf1\to V_n\otimes V_n\) and \(C_n:V_n\otimes V_n\to\mathbf1\); exactness includes both snake identities. All ordered tensor factors below retain their displayed order. Composition \(f;g\) means first \(f\), then \(g\). Write \(f\mathbin{\star}g\) for composition with the canonical associators and unitors inserted; it does not permute strands. Right and left whiskering are denoted \(f\triangleright A\) and \(A\triangleleft f\).
--
--   The following are assumed category axioms, not conclusions:
--
--   1. For every \(n\) and every endomorphism \(f\) of \(V_n\), there is a unique \(s\in K\) such that \(f=s\,\mathrm{id}_{V_n}\).
--   2. Every map \(V_a\to V_b\) is zero when \(a\ne b\).
--   3. For every \(a,b\), there exist maps \(i_c:V_c\to V_a\otimes V_b\) and \(p_c:V_a\otimes V_b\to V_c\), indexed by all natural \(c\), such that \(i_c;p_c=\mathrm{id}_{V_c}\) for admissible \(c\le a+b\), and \(\sum_c p_c;i_c=\mathrm{id}_{V_a\otimes V_b}\), summing over precisely those channels. These existential maps are not stipulated to equal the chosen vertex maps below.
--   4. \(D_n;C_n=\iota(\Delta(n))\,\mathrm{id}_{\mathbf1}\).
--
--   A triple of integers \((a,b,c)\) is admissible exactly when all three entries are nonnegative, all three triangle inequalities hold, and \(a+b+c\) is even. Put
--   \[
--   [n]=\frac{q^n-q^{-n}}{q-q^{-1}},\qquad
--   [n]!=\begin{cases}0&n<0,\\\prod_{r=1}^n[r]&n\ge0,\end{cases}
--   \qquad \Delta(n)=\begin{cases}(-1)^n[n+1]&n\ge0,\\0&n<0.\end{cases}
--   \]
--   For admissible \((a,b,c)\), with \(s=(a+b+c)/2\), define
--   \[
--   \theta(a,b,c)=(-1)^s\frac{[s+1]![s-a]![s-b]![s-c]!}{[a]![b]![c]!};
--   \]
--   otherwise it is zero.
--
--   Choose arbitrary trivalent covectors \(t_{abc}:V_a\otimes V_b\otimes V_c\to\mathbf1\). The following formulas specify all bent vertices exactly, including reversals of labels. Identity maps at the ends of these formulas are retained to indicate canonical regrouping:
--   \[
--   \begin{aligned}
--   t^{abc}={}&D_c\star(V_c\triangleleft(D_b\triangleright V_c))
--   \star\bigl(V_c\triangleleft((V_b\triangleleft(D_a\triangleright V_b))\triangleright V_c)\bigr)
--   \star(t_{cba}\triangleright(V_a\otimes V_b\otimes V_c))\star\mathrm{id},\\
--   s_l^{ab}={}&\mathrm{id}\star(D_a\triangleright V_l)
--   \star\bigl(V_a\triangleleft((D_b\triangleright V_a)\triangleright V_l)\bigr)
--   \star(V_a\triangleleft V_b\triangleleft t_{bal})\star\mathrm{id},\\
--   f_{ab}^{l}={}&\mathrm{id}\star((V_a\otimes V_b)\triangleleft D_l)
--   \star(t_{abl}\triangleright V_l)\star\mathrm{id}.
--   \end{aligned}
--   \]
--   Here \(t^{abc}\) has outputs \(a,b,c\), \(s_l^{ab}:V_l\to V_a\otimes V_b\), and \(f_{ab}^{l}:V_a\otimes V_b\to V_l\). The superscripted vertex is a linear cup-bending construction, not a Hermitian adjoint.
--
--   The vertex-normalization hypothesis has exactly two fields:
--   \[
--   t^{abc};t_{abc}=\iota(\theta(a,b,c))\,\mathrm{id}_{\mathbf1},
--   \]
--   and cyclicity \(R(t_{abc})=t_{bca}\), where the exact rotation is
--   \[
--   R(t_{abc})=\mathrm{id}\star(D_a\triangleright(V_b\otimes V_c\otimes V_a))
--   \star\bigl(V_a\triangleleft(t_{abc}\triangleright V_a)\bigr)\star C_a.
--   \]
--
--   There is also a separate seed hypothesis. Define
--   \[
--   X_{abcd;l}=D_l\star(s_l^{ab}\otimes s_l^{cd})\star\mathrm{id},\qquad
--   H^R_{abcd;l}=\mathrm{id}\star\bigl(V_a\triangleleft(f_{bc}^{l}\triangleright V_d)\bigr)\star t_{ald}.
--   \]
--   For signed channels \(j,l\), the graphical tetrahedron is
--   \[
--   T(a,b,c,d;j,l)=
--   \begin{cases}X_{adcb;j};H^R_{adcb;l}&j,l\ge0,\\0&\text{otherwise}.\end{cases}
--   \]
--   The boundary order is exactly \(a,d,c,b\), the first channel \(j\) labels the cup in \(X\), and the last channel \(l\) is the inner horizontal rung. The seed assumes, for all natural \(a,b,c,d,j\),
--   \[
--   T(a,b,c,d;j,2)=\iota(\mathcal T(a,b,c,d;j,2))\,\mathrm{id}_{\mathbf1}.
--   \]
--   It is additional initial-value data, not a field of vertex normalization, and not a conclusion that arbitrary channels agree with a scalar sum.
--
--   For completeness the seed's scalar \(\mathcal T\) is independently defined as follows. Set
--   \[
--   A=\left(\frac{a+d+j}{2},\frac{b+c+j}{2},\frac{a+b+l}{2},\frac{c+d+l}{2}\right),\quad
--   B=\left(\frac{b+d+j+l}{2},\frac{a+c+j+l}{2},\frac{a+b+c+d}{2}\right).
--   \]
--   If \((a,d,j),(b,c,j),(a,b,l),(c,d,l)\) are all admissible, then
--   \[
--   \mathcal T(a,b,c,d;j,l)=
--   \frac{\prod_{i=1}^4\prod_{r=1}^3[B_r-A_i]!}{[a]![b]![c]![d]![j]![l]!}
--   \sum_{z=0}^{a+b+c+d+j+l}
--   \frac{(-1)^z[z+1]!}{\prod_{i=1}^4[z-A_i]!\prod_{r=1}^3[B_r-z]!};
--   \]
--   otherwise it is zero. Integer halves use integer division; admissibility makes the displayed halves integral in the nonzero branch.
--
--   ## The three asserted conclusions
--
--   Define the two-leg operator and its four-leg extension by
--   \[
--   K_{ab}=\iota([a][b])\,
--   \bigl((s_a^{a2}\triangleright V_b)\star(V_a\triangleleft f_{2b}^{b})\bigr),\qquad
--   \widehat K_{abcd}=\mathrm{id}\star(K_{ab}\triangleright(V_c\otimes V_d))\star\mathrm{id}.
--   \]
--   Thus the label-2 rung is split from the \(a\) strand and fused into the \(b\) strand, with exactly the prefactor \([a][b]\), not a divided or square-root prefactor.
--
--   For admissible \((a,b,l)\), put
--   \[
--   \lambda_{ab}(l)=
--   \frac{[(a-b+l)/2][(-a+b+l)/2]-[(a+b-l)/2][(a+b+l)/2+2]}{[2]},
--   \]
--   and put \(\lambda_{ab}(l)=0\) otherwise. The \(+2\) is inside the last quantum integer, after taking the half.
--
--   Under all the preceding hypotheses, the statement asserts their conjunction:
--
--   1. For every natural \(a,b,l\), the closed rung satisfies
--      \[
--      D_l;\bigl((s_l^{ab};K_{ab};f_{ab}^{l})\triangleright V_l\bigr);C_l
--      =\iota([a][b])\,T(a,a,b,b;l,2).
--      \]
--      In particular the right-hand tetrahedron expands as \(X_{abba;l};H^R_{abba;2}\). This is a claimed graphical closure identification, not an additional hypothesis; the separate seed only evaluates its already-defined right-hand side as a scalar.
--   2. For every natural \(a,b,l\),
--      \[
--      s_l^{ab};K_{ab}=\iota(\lambda_{ab}(l))\,s_l^{ab}.
--      \]
--   3. For every natural \(a,b,c,d,l\),
--      \[
--      X_{abcd;l};\widehat K_{abcd}=\iota(\lambda_{ab}(l))\,X_{abcd;l}.
--      \]
--
--   There are no admissibility or nonzero-state hypotheses restricting these quantifiers. In particular the last two equations do not assert that the displayed maps are nonzero eigenvectors, nor that they form a basis. No recurrence or global tetrahedral evaluation is assumed.
--
--   ## Division and logical scope
--
--   All scalar divisions are total field divisions in rational-function fields: \(0^{-1}=0\), hence \(x/0=0\). The formulas impose no implicit denominator-nonvanishing hypotheses. Negative factorials and inadmissible channels are deliberate zero extensions. These conventions do not define evaluation at a complex pole or assert a root-of-unity specialization. The three identities are the asserted theorem statement; no proof of them is supplied here.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015), https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eqs. (12)–(15), rung operator, triangle evaluation and eigenvalue.

import Definitions.Def_QuantumSixJNetwork

open CategoryTheory MonoidalCategory
open scoped BigOperators QuantumSixJ

universe v u

namespace QuantumSixJ.Network

theorem rung_eigenvalue {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) (hSeed : TetSeed W) :
    (∀ a b l : ℕ,
      S.cup l ≫ ((W.split l a b ≫ W.K2 a b ≫ W.fuse a b l) ▷ S.V l) ≫ S.cap l =
        ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) • W.tet a a b b l 2) ∧
    (∀ a b l : ℕ,
      W.split l a b ≫ W.K2 a b = ι (Λ a b l) • W.split l a b) ∧
    (∀ a b c d l : ℕ,
      W.X a b c d l ≫ W.Kop a b c d = ι (Λ a b l) • W.X a b c d l) := by sorry

end QuantumSixJ.Network
