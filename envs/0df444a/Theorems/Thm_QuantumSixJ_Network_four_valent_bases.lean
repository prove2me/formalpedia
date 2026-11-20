-- Prove2me | Theorems.Thm_QuantumSixJ_Network_four_valent_bases
-- name    : QuantumSixJ.Network.four_valent_bases
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:44:24.207191+00:00
-- url     : https://prove2.me/theorems/63ca57e8-82fd-471f-b929-ea9be300afe8
-- title:
--   Eqs. (6)–(10) — four-valent bases and recoupling
-- statement:
--   Let $\mathcal C$ be a $K$-linear preadditive monoidal category, $K=\mathbb C(q)$, with additive and $K$-linear tensor product. The chosen objects $V_n$ for natural labels satisfy $V_0\cong\mathbb1$ and have exact self-pairings. Assume `SuQ2Axioms`: unique scalar endomorphisms of each $V_n$, zero morphisms between different labels, the admissible $\mathrm{SL}(2)$ fusion decompositions, and the loop values $\Delta_n$. Choose trivalent vertices $W$, and assume `VertexNormalized W`: theta normalization and cyclicity. Scalars act through $\iota:\mathbb Q(q)\hookrightarrow K$, fixing $q$. Composition $f;g$ means first $f$, then $g$.
--
--   Without `TetSeed`, prove the complete four-valent basis and recoupling statement for every natural $a,b,c,d$:
--   1. $H_k;H_j^R=\delta_{kj}\iota(h_j)\mathrm{id}_{\mathbb1}$ and $X_m;X_l^R=\delta_{ml}\iota(x_l)\mathrm{id}_{\mathbb1}$, including inadmissible channels.
--   2. Every state $f:\mathbb1\to V_a\otimes V_b\otimes V_c\otimes V_d$ has scalar pairing coefficients in each basis and equals its corresponding orthogonal expansion. Every covector has the dual expansion as well. Horizontal sums run over $0\le j\le b+c$ and vertical sums over $0\le l\le a+b$; coefficients are divided by the respective norms.
--   3. Prove the diagram identification
--   $$X(a,b,c,d;l);H^R(a,b,c,d;j)=T(a,b,c,d;j,l),$$
--   where the right-hand side is the explicitly defined graphical network $X(a,d,c,b;j);H^R(a,d,c,b;l)$. This equality is a conclusion to establish, not an extra hypothesis or an assumed change of notation.
--   4. For every $l$, scalar coefficients $s_j$ exist with $T(a,b,c,d;j,l)=s_j\mathrm{id}_{\mathbb1}$ and
--   $$X_l=\sum_{j=0}^{b+c}\frac{s_j}{\iota(h_j)}H_j.$$
--   The statement includes coefficient existence rather than presupposing that all closures have already been evaluated. Division by zero follows the specified zero-extension convention.
--
--   ### Independent mathematical read-back
--
--   # Four-valent pairings and expansions
--
--   Let \(K=\mathbb C(q)\), and let \(\iota:\mathbb Q(q)\to K\) be the coefficient embedding fixing \(q\). Work in an arbitrary preadditive \(K\)-linear monoidal category with tensor product additive and \(K\)-linear in both variables. Write \(\mathbf1\) for the tensor unit. Composition \(f\gg g\) means first \(f\), then \(g\); canonical associators and unitors are implicit, never permutations of tensor factors.
--
--   ## Hypotheses and notation
--
--   For each natural \(a\), an object \(V_a\) is given, together with \(V_0\cong\mathbf1\) and a self-duality cup \(u_a\) and cap \(e_a\) satisfying both snake identities. There is a chosen covariant vertex \(v_{abc}:V_a\otimes V_b\otimes V_c\to\mathbf1\) for every natural triple.
--
--   A triple \((a,b,c)\) is admissible when its entries are nonnegative, satisfy all three triangle inequalities, and have even sum. The assumed category axioms are: every endomorphism of \(V_a\) is a unique scalar multiple of its identity; all morphisms between distinctly labelled objects vanish; for every \(a,b\) there exist maps \(i_c:V_c\to V_a\otimes V_b\) and \(p_c:V_a\otimes V_b\to V_c\), for all natural \(c\), with \(i_c\gg p_c=\operatorname{id}_{V_c}\) for admissible \(c\le a+b\), and \(\sum_{c\le a+b,\ (a,b,c)\text{ admissible}}p_c\gg i_c=\operatorname{id}_{V_a\otimes V_b}\); and \(u_a\gg e_a=\iota(\Delta(a))\operatorname{id}_{\mathbf1}\).
--
--   Set \([n]=(q^n-q^{-n})/(q-q^{-1})\), with \([n]!=0\) for negative integer \(n\), and \([n]!=\prod_{k=1}^n[k]\) otherwise. For natural \(a\), \(\Delta(a)=(-1)^a[a+1]\). For admissible \((a,b,c)\), put \(s=(a+b+c)/2\) and
--   \[
--   \theta(a,b,c)=(-1)^s\frac{[s+1]![s-a]![s-b]![s-c]!}{[a]![b]![c]!};
--   \]
--   set \(\theta=0\) otherwise.
--
--   Whiskers \(A\triangleleft f\) and \(f\triangleright A\) mean \(\operatorname{id}_A\otimes f\) and \(f\otimes\operatorname{id}_A\). With \(A=V_a,B=V_b,C'=V_c,L=V_l\), the upward vertex, split, and fuse are the following ordered composites, with only canonical regrouping suppressed:
--   \[
--   \begin{aligned}
--   v^{abc}&=u_c\gg(C'\triangleleft(u_b\triangleright C'))\gg
--   \bigl(C'\triangleleft((B\triangleleft(u_a\triangleright B))\triangleright C')\bigr)
--   \gg(v_{cba}\triangleright(A\otimes B\otimes C')),\\
--   \operatorname{split}_{l;a,b}&=(u_a\triangleright L)\gg
--   \bigl(A\triangleleft((u_b\triangleright A)\triangleright L)\bigr)
--   \gg(A\triangleleft B\triangleleft v_{bal}),\\
--   \operatorname{fuse}_{a,b;l}&=((A\otimes B)\triangleleft u_l)\gg(v_{abl}\triangleright L).
--   \end{aligned}
--   \]
--   Vertex normalization assumes exactly \(v^{abc}\gg v_{abc}=\iota(\theta(a,b,c))\operatorname{id}_{\mathbf1}\), and that
--   \[
--   (u_a\triangleright(B\otimes C'\otimes A))\gg
--   \bigl(A\triangleleft(v_{abc}\triangleright A)\bigr)\gg e_a=v_{bca}
--   \]
--   for every natural triple. There is **no tetrahedral seed hypothesis**, no all-channel identification with a scalar tetrahedral sum, and no assumed general tetrahedral symmetry. No braiding or Hermitian structure is assumed.
--
--   Fix arbitrary \(a,b,c,d\in\mathbb N\), with no admissibility restriction, and write \(B_{abcd}=V_a\otimes V_b\otimes V_c\otimes V_d\), left-associated. The states and covectors are
--   \[
--   \begin{aligned}
--   X_l&=u_l\gg(\operatorname{split}_{l;a,b}\otimes\operatorname{split}_{l;c,d}),&
--   X_l^R&=(\operatorname{fuse}_{a,b;l}\otimes\operatorname{fuse}_{c,d;l})\gg e_l,\\
--   H_j&=v^{ajd}\gg\bigl(V_a\triangleleft(\operatorname{split}_{j;b,c}\triangleright V_d)\bigr),&
--   H_j^R&=\bigl(V_a\triangleleft(\operatorname{fuse}_{b,c;j}\triangleright V_d)\bigr)\gg v_{ajd}.
--   \end{aligned}
--   \]
--   States go from \(\mathbf1\) to \(B_{abcd}\), covectors in the reverse direction. The superscript \(R\) denotes these explicitly defined covectors, not a conjugate-linear adjoint.
--
--   Define rational-function norms
--   \[
--   h_j=\begin{cases}\theta(a,d,j)\theta(b,c,j)/\Delta(j),& (a,d,j),(b,c,j)\text{ admissible},\\0,&\text{otherwise},\end{cases}
--   \quad
--   x_l=\begin{cases}\theta(a,b,l)\theta(c,d,l)/\Delta(l),& (a,b,l),(c,d,l)\text{ admissible},\\0,&\text{otherwise}.\end{cases}
--   \]
--   They are bilinear pairing scalars, not positive or Hermitian norms.
--
--   ## The eight conclusions
--
--   For every fixed natural quadruple \((a,b,c,d)\), the assertion is the conjunction of the following eight statements.
--
--   1. For **every** \(j,k\in\mathbb N\),
--      \[
--      H_k\gg H_j^R=\begin{cases}\iota(h_j)\operatorname{id}_{\mathbf1},&k=j,\\0,&k\ne j.\end{cases}
--      \]
--   2. For **every** \(l,m\in\mathbb N\),
--      \[
--      X_m\gg X_l^R=\begin{cases}\iota(x_l)\operatorname{id}_{\mathbf1},&m=l,\\0,&m\ne l.\end{cases}
--      \]
--   3. For every state \(f:\mathbf1\to B_{abcd}\), there exists a function \(s:\mathbb N\to K\) such that, simultaneously,
--      \[
--      \forall j\in\mathbb N,\quad f\gg H_j^R=s(j)\operatorname{id}_{\mathbf1},\qquad
--      f=\sum_{j=0}^{b+c}\frac{s(j)}{\iota(h_j)}H_j.
--      \]
--   4. For every covector \(g:B_{abcd}\to\mathbf1\), there exists a function \(s:\mathbb N\to K\) such that
--      \[
--      \forall j\in\mathbb N,\quad H_j\gg g=s(j)\operatorname{id}_{\mathbf1},\qquad
--      g=\sum_{j=0}^{b+c}\frac{s(j)}{\iota(h_j)}H_j^R.
--      \]
--   5. For every state \(f:\mathbf1\to B_{abcd}\), there exists a function \(s:\mathbb N\to K\) such that
--      \[
--      \forall l\in\mathbb N,\quad f\gg X_l^R=s(l)\operatorname{id}_{\mathbf1},\qquad
--      f=\sum_{l=0}^{a+b}\frac{s(l)}{\iota(x_l)}X_l.
--      \]
--   6. For every covector \(g:B_{abcd}\to\mathbf1\), there exists a function \(s:\mathbb N\to K\) such that
--      \[
--      \forall l\in\mathbb N,\quad X_l\gg g=s(l)\operatorname{id}_{\mathbf1},\qquad
--      g=\sum_{l=0}^{a+b}\frac{s(l)}{\iota(x_l)}X_l^R.
--      \]
--      In statements 3–6 the existential functions are independently chosen for the given morphism and expansion. The pairing equalities cover all natural indices, even outside the finite sum. The sums range over **all** integers from zero through the displayed inclusive upper endpoint, not filtered admissible ranges. The statement does not explicitly assert uniqueness of these functions or nonzero norms at every summed index.
--   7. For every \(j,l\in\mathbb N\),
--      \[
--      X_l(a,b,c,d)\gg H_j^R(a,b,c,d)=\operatorname{Tet}(a,b,c,d;j,l).
--      \]
--      The tetrahedral endomorphism is defined, for integer channels \(r,t\), by
--      \[
--      \operatorname{Tet}(a,b,c,d;r,t)=
--      \begin{cases}
--      X_r(a,d,c,b)\gg H_t^R(a,d,c,b),&r,t\ge0,\\0,&\text{otherwise}.
--      \end{cases}
--      \]
--      Thus the **literal unfolded assertion** here, since \(j,l\) are natural, is
--      \[
--      \boxed{X_l(a,b,c,d)\gg H_j^R(a,b,c,d)
--      =X_j(a,d,c,b)\gg H_l^R(a,d,c,b).}
--      \]
--      More explicitly, the left composite is
--      \[
--      u_l\gg(\operatorname{split}_{l;a,b}\otimes\operatorname{split}_{l;c,d})
--      \gg\bigl(V_a\triangleleft(\operatorname{fuse}_{b,c;j}\triangleright V_d)\bigr)\gg v_{ajd},
--      \]
--      whereas the right composite is
--      \[
--      u_j\gg(\operatorname{split}_{j;a,d}\otimes\operatorname{split}_{j;c,b})
--      \gg\bigl(V_a\triangleleft(\operatorname{fuse}_{d,c;l}\triangleright V_b)\bigr)\gg v_{alb}.
--      \]
--      This is a substantive equality between closures with boundary orders \((a,b,c,d)\) and \((a,d,c,b)\) and interchanged channel roles, not merely the defining formula for Tet. Pure substitution into that definition instead gives the left closure as \(\operatorname{Tet}(a,d,c,b;l,j)\); the assertion therefore equates that endomorphism with \(\operatorname{Tet}(a,b,c,d;j,l)\).
--   8. For every \(l\in\mathbb N\), there exists a function \(s:\mathbb N\to K\) such that
--      \[
--      \forall j\in\mathbb N,\quad \operatorname{Tet}(a,b,c,d;j,l)=s(j)\operatorname{id}_{\mathbf1},\qquad
--      X_l(a,b,c,d)=\sum_{j=0}^{b+c}\frac{s(j)}{\iota(h_j)}H_j(a,b,c,d).
--      \]
--      This expands each **vertical state in horizontal states**, not the reverse expansion. It asserts scalar existence for every Tet in this natural-channel family, but does not give a numerical formula for those scalars or identify them with a separately defined finite-sum tetrahedral evaluation. The same function supplies both all-channel scalar equalities and the finite expansion, and may depend on \(a,b,c,d,l\).
--
--   All divisions are total divisions in a rational-function field, so a zero denominator yields zero. No nonvanishing hypotheses or restrictions to a complex specialization are added. These are pairings and spanning assertions for the full natural-indexed families, not a claim that every indexed state is a nonzero basis element. The tetrahedral symmetry in statement 7 is among the conclusions to establish, not among the assumptions.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015), https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eqs. (5)–(10), coupled four-valent networks, graphical Tet, orthogonality, norms and recoupling expansion.

import Definitions.Def_QuantumSixJNetwork

open CategoryTheory MonoidalCategory
open scoped BigOperators QuantumSixJ

universe v u

namespace QuantumSixJ.Network

theorem four_valent_bases {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) :
    ∀ a b c d : ℕ,
      (∀ j k : ℕ, W.H a b c d k ≫ W.Hcov a b c d j =
        if k = j then ι (h a b c d j) • 𝟙 (𝟙_ C) else 0) ∧
      (∀ l m : ℕ, W.X a b c d m ≫ W.Xcov a b c d l =
        if m = l then ι (x a b c d l) • 𝟙 (𝟙_ C) else 0) ∧
      (∀ f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d,
        ∃ s : ℕ → K,
          (∀ j : ℕ, f ≫ W.Hcov a b c d j = s j • 𝟙 (𝟙_ C)) ∧
          f = ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.H a b c d j) ∧
      (∀ g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C,
        ∃ s : ℕ → K,
          (∀ j : ℕ, W.H a b c d j ≫ g = s j • 𝟙 (𝟙_ C)) ∧
          g = ∑ j ∈ Finset.range (b + c + 1), (s j / ι (h a b c d j)) • W.Hcov a b c d j) ∧
      (∀ f : 𝟙_ C ⟶ S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d,
        ∃ s : ℕ → K,
          (∀ l : ℕ, f ≫ W.Xcov a b c d l = s l • 𝟙 (𝟙_ C)) ∧
          f = ∑ l ∈ Finset.range (a + b + 1), (s l / ι (x a b c d l)) • W.X a b c d l) ∧
      (∀ g : S.V a ⊗ S.V b ⊗ S.V c ⊗ S.V d ⟶ 𝟙_ C,
        ∃ s : ℕ → K,
          (∀ l : ℕ, W.X a b c d l ≫ g = s l • 𝟙 (𝟙_ C)) ∧
          g = ∑ l ∈ Finset.range (a + b + 1), (s l / ι (x a b c d l)) • W.Xcov a b c d l) ∧
      (∀ j l : ℕ, W.X a b c d l ≫ W.Hcov a b c d j = W.tet a b c d j l) ∧
      (∀ l : ℕ, ∃ s : ℕ → K,
        (∀ j : ℕ, W.tet a b c d j l = s j • 𝟙 (𝟙_ C)) ∧
        W.X a b c d l = ∑ j ∈ Finset.range (b + c + 1),
          (s j / ι (h a b c d j)) • W.H a b c d j) := by sorry

end QuantumSixJ.Network
