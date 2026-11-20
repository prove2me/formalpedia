-- Prove2me | Theorems.Thm_QuantumSixJ_Network_diagram_calculus
-- name    : QuantumSixJ.Network.diagram_calculus
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:44:18.645556+00:00
-- url     : https://prove2.me/theorems/50dfc732-e6c4-445e-99e1-336a6b0184ed
-- title:
--   Eqs. (2)–(5) — bubble, vertex-collapse and fusion identities
-- statement:
--   Let $\mathcal C$ be a $K$-linear preadditive monoidal category, $K=\mathbb C(q)$, with additive and $K$-linear tensor product. The chosen objects $V_n$ for natural labels satisfy $V_0\cong\mathbb1$ and have exact self-pairings. Assume `SuQ2Axioms`: unique scalar endomorphisms of each $V_n$, zero morphisms between different labels, the admissible $\mathrm{SL}(2)$ fusion decompositions, and the loop values $\Delta_n$. Choose trivalent vertices $W$, and assume `VertexNormalized W`: theta normalization and cyclicity. Scalars act through $\iota:\mathbb Q(q)\hookrightarrow K$, fixing $q$. Composition $f;g$ means first $f$, then $g$.
--
--   Prove the following local diagram identities, without `TetSeed`:
--   1. For every natural triple, splitting $c$ into $a,b$ and then fusing gives
--   $$\operatorname{split}_{c;ab};\operatorname{fuse}_{ab;c}=\frac{\iota(\theta(a,b,c))}{\iota(\Delta_c)}\,\mathrm{id}_{V_c}.$$
--   2. The chosen trivalent vertex is zero on every inadmissible triple.
--   3. Every morphism $V_a\otimes V_b\otimes V_c\to\mathbb1$ is a scalar multiple of that vertex. Existence, not uniqueness of the scalar, is asserted on inadmissible triples.
--   4. For every $a,b\in\mathbb N$,
--   $$\mathrm{id}_{V_a\otimes V_b}=\sum_{c\in F(a,b)}\frac{\iota(\Delta_c)}{\iota(\theta(a,b,c))}\,(\operatorname{fuse}_{ab;c};\operatorname{split}_{c;ab}),$$
--   where $F(a,b)$ is the finite admissible fusion range. All coefficients follow the total-field division convention.
--
--   ### Independent mathematical read-back
--
--   # Trivalent diagram calculus
--
--   Work over the rational-function field \(K=\mathbb C(q)\), with coefficient embedding \(\iota:\mathbb Q(q)\to K\) fixing \(q\). Let \(C\) be a preadditive \(K\)-linear monoidal category whose tensor product is additive and \(K\)-linear in each variable. The object and morphism universes are arbitrary. Write \(\mathbf1\) for its tensor unit. Composition \(f\gg g\) means first \(f\), then \(g\); tensor products below retain their written factor order and use the canonical associators and unitors.
--
--   ## Data and hypotheses
--
--   There are objects \(V_a\) for every \(a\in\mathbb N\), an isomorphism \(V_0\cong\mathbf1\), and a specified self-duality pairing for each \(V_a\). Its cup \(u_a:\mathbf1\to V_a\otimes V_a\) and cap \(e_a:V_a\otimes V_a\to\mathbf1\) satisfy both snake identities. A chosen vertex is a morphism
--   \[
--   v_{abc}:(V_a\otimes V_b)\otimes V_c\longrightarrow\mathbf1
--   \]
--   for every natural triple, not just admissible triples.
--
--   A triple of integer labels is admissible when all three are nonnegative, each is at most the sum of the other two, and their sum is even. Put
--   \[
--   F(a,b)=\{c\in\mathbb N:0\le c\le a+b,\ (a,b,c)\text{ admissible}\}.
--   \]
--   The category hypotheses are exactly:
--
--   * Every endomorphism of each \(V_a\) is a unique scalar multiple of its identity.
--   * For \(a\ne b\), every morphism \(V_a\to V_b\) is zero.
--   * For each \(a,b\), there exist families \(i_c:V_c\to V_a\otimes V_b\) and \(p_c:V_a\otimes V_b\to V_c\), defined for all natural \(c\), such that \(i_c\gg p_c=\operatorname{id}_{V_c}\) for \(c\in F(a,b)\), and \(\sum_{c\in F(a,b)}p_c\gg i_c=\operatorname{id}_{V_a\otimes V_b}\). These families are not assumed to be the chosen vertex's split and fuse maps.
--   * \(u_a\gg e_a=\iota(\Delta(a))\operatorname{id}_{\mathbf1}\) for all natural \(a\).
--
--   Here \([n]=(q^n-q^{-n})/(q-q^{-1})\), \([n]!=0\) for negative integers \(n\), and \([n]!=\prod_{k=1}^n[k]\) otherwise. For natural \(a\), \(\Delta(a)=(-1)^a[a+1]\). For an admissible triple, with \(s=(a+b+c)/2\),
--   \[
--   \theta(a,b,c)=(-1)^s\frac{[s+1]![s-a]![s-b]![s-c]!}{[a]![b]![c]!};
--   \]
--   otherwise \(\theta=0\).
--
--   To specify the vertex normalization and the derived maps, write \(A=V_a,B=V_b,C'=V_c\), and suppress only canonical regrouping. The upward vertex \(v^{abc}:\mathbf1\to A\otimes B\otimes C'\) is the composite
--   \[
--   u_c\gg(C'\triangleleft(u_b\triangleright C'))\gg
--   \bigl(C'\triangleleft((B\triangleleft(u_a\triangleright B))\triangleright C')\bigr)
--   \gg(v_{cba}\triangleright(A\otimes B\otimes C')).
--   \]
--   Whiskering \(A\triangleleft f\) means \(\operatorname{id}_A\otimes f\), and \(f\triangleright A\) means \(f\otimes\operatorname{id}_A\). The normalization assumes, for every natural triple,
--   \(v^{abc}\gg v_{abc}=\iota(\theta(a,b,c))\operatorname{id}_{\mathbf1}\).
--   It also assumes cyclicity: the composite
--   \[
--   (u_a\triangleright(B\otimes C'\otimes A))\gg
--   \bigl(A\triangleleft(v_{abc}\triangleright A)\bigr)\gg e_a
--   \]
--   equals \(v_{bca}\). No tetrahedral seed evaluation is assumed. No symmetry, braiding, Hermitian adjoint, or additional arbitrary-map rotation law is included among the hypotheses.
--
--   For \(L=V_c\), the derived maps used in the conclusion are
--   \[
--   \begin{aligned}
--   \operatorname{split}_{c;a,b}
--    &= (u_a\triangleright L)\gg
--    \bigl(A\triangleleft((u_b\triangleright A)\triangleright L)\bigr)
--    \gg(A\triangleleft B\triangleleft v_{bac}),\\
--   \operatorname{fuse}_{a,b;c}
--    &=((A\otimes B)\triangleleft u_c)\gg(v_{abc}\triangleright L).
--   \end{aligned}
--   \]
--   Thus split goes from \(V_c\) to \(V_a\otimes V_b\), and fuse goes in the opposite direction.
--
--   ## The four conclusions
--
--   Under precisely these hypotheses, the assertion is the conjunction of:
--
--   1. For every \(a,b,c\in\mathbb N\), including inadmissible triples,
--      \[
--      \operatorname{split}_{c;a,b}\gg\operatorname{fuse}_{a,b;c}
--      =\frac{\iota(\theta(a,b,c))}{\iota(\Delta(c))}\operatorname{id}_{V_c}.
--      \]
--      This is split followed by fuse, an endomorphism of the single labelled object.
--   2. For every natural \(a,b,c\), if \((a,b,c)\) is not admissible, then \(v_{abc}=0\).
--   3. For every natural \(a,b,c\) and every morphism \(f:V_a\otimes V_b\otimes V_c\to\mathbf1\), there exists \(t\in K\) such that \(f=t\,v_{abc}\). Existence, not uniqueness of \(t\), is asserted; admissibility is not required. In particular the wording is a spanning statement, not an assertion that every vertex is a nonzero basis vector.
--   4. For every \(a,b\in\mathbb N\),
--      \[
--      \sum_{c\in F(a,b)}\frac{\iota(\Delta(c))}{\iota(\theta(a,b,c))}
--      \bigl(\operatorname{fuse}_{a,b;c}\gg\operatorname{split}_{c;a,b}\bigr)
--      =\operatorname{id}_{V_a\otimes V_b}.
--      \]
--      The summands first fuse and then split. The finite range is exactly the admissible labels among \(0,\ldots,a+b\).
--
--   All coefficients are rational-function field expressions, with total field division (in particular division by zero evaluates to zero). There are no additional nonvanishing or complex-specialization hypotheses. The statement supplies no numerical tetrahedral evaluation and no recurrence.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015), https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eqs. (2)–(5), bubble, vertex-collapse and fusion calculus.

import Definitions.Def_QuantumSixJNetwork

open CategoryTheory MonoidalCategory
open scoped BigOperators QuantumSixJ

universe v u

namespace QuantumSixJ.Network

theorem diagram_calculus {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) :
    (∀ a b c : ℕ,
      W.split c a b ≫ W.fuse a b c =
        (ι (θ a b c) / ι (Δ c)) • 𝟙 (S.V c)) ∧
    (∀ a b c : ℕ, ¬ Admissible (a : ℤ) b c → W.vertex a b c = 0) ∧
    (∀ (a b c : ℕ) (f : S.V a ⊗ S.V b ⊗ S.V c ⟶ 𝟙_ C),
      ∃ t : K, f = t • W.vertex a b c) ∧
    (∀ a b : ℕ,
      (∑ c ∈ fusionRange a b,
        (ι (Δ c) / ι (θ a b c)) • (W.fuse a b c ≫ W.split c a b)) =
          𝟙 (S.V a ⊗ S.V b)) := by sorry

end QuantumSixJ.Network
