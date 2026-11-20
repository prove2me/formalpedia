-- Prove2me | Theorems.Thm_QuantumSixJ_Network_matrix_entries
-- name    : QuantumSixJ.Network.matrix_entries
-- status  : Proved
-- author  : @igor.kh
-- created : 2026-11-13T00:44:21.261126+00:00
-- url     : https://prove2.me/theorems/4b4e7be3-09b3-42a3-8119-ccba89152c93
-- title:
--   Eqs. (16)–(20) — symmetric tridiagonal matrix entries
-- statement:
--   Let $\mathcal C$ be a $K$-linear preadditive monoidal category, $K=\mathbb C(q)$, with additive and $K$-linear tensor product. The chosen objects $V_n$ for natural labels satisfy $V_0\cong\mathbb1$ and have exact self-pairings. Assume `SuQ2Axioms`: unique scalar endomorphisms of each $V_n$, zero morphisms between different labels, the admissible $\mathrm{SL}(2)$ fusion decompositions, and the loop values $\Delta_n$. Choose trivalent vertices $W$, and assume `VertexNormalized W`: theta normalization and cyclicity. Scalars act through $\iota:\mathbb Q(q)\hookrightarrow K$, fixing $q$. Composition $f;g$ means first $f$, then $g$.
--
--   Also assume the separate initial data `TetSeed W`: for every natural $a,b,c,d,j$, $T(a,b,c,d;j,2)=\iota(\operatorname{Tet}^{\mathrm{sum}}(a,b,c,d;j,2))\,\mathrm{id}_{\mathbb1}$. These are seed values, not an all-channel network-to-sum identity.
--
--   Let $M_{jk}=H_k;\mathrm{Kop};H_j^R$. Prove all of the following, for every natural choice of external and channel labels:
--   1. Identify each of the two literal four-vertex closures in the formal statement with the graphical networks $T(a,a,k,j;d,2)$ and $T(b,b,k,j;c,2)$, respectively. The first closure inserts a split on the $a$ strand of $\operatorname{vertexUp}(a,k,d)$ and fuses $2,k$ to $j$; the second closes the triangle obtained by splitting $k$ to $b,c$, fusing $2,b$ to $b$, and then $b,c$ to $j$.
--   2. Establish the exact factorization
--   $$M_{jk}=\frac{\iota([a][b])}{\iota(\theta(2,k,j))}\,\bigl(T(a,a,k,j;d,2);T(b,b,k,j;c,2)\bigr).$$
--   3. Independently show $M_{jk}=0$ when $(2,k,j)$ is inadmissible, so the central zero-theta case is included rather than discarded by cancellation.
--   4. Establish the complete numerical matrix evaluation
--   $$M_{jk}=\iota(L_{jk})\mathrm{id}_{\mathbb1}.$$
--   Thus the categorical matrix is symmetric and tridiagonal, including both off-diagonals, all inadmissible channels, and $M_{00}=0$. The closure identifications and numerical evaluation are conclusions of the theorem, not additional seed assumptions.
--
--   ### Independent mathematical read-back
--
--   # Horizontal matrix entries
--
--   ## Setting and all assumptions
--
--   Let \(F=\mathbb Q(q)\), \(K=\mathbb C(q)\), with \(q\) indeterminate and coefficient embedding \(\iota:F\to K\) fixing \(q\). Let \(\mathcal C\) be a category in arbitrary object and morphism universes, assumed preadditive, \(K\)-linear, monoidal, monoidally preadditive, and monoidally \(K\)-linear. No braiding, symmetric structure, dagger, positivity, or concrete representation category is assumed.
--
--   There are labelled objects \(V_n\), \(n\in\mathbb N\), a chosen isomorphism \(V_0\cong\mathbf1\), and chosen exact self-pairings giving cups \(D_n:\mathbf1\to V_n\otimes V_n\) and caps \(C_n:V_n\otimes V_n\to\mathbf1\) satisfying both snake identities. Assume:
--
--   * Every endomorphism of \(V_n\) is a unique \(K\)-scalar multiple of its identity.
--   * Every morphism between differently labelled objects is zero.
--   * For each \(a,b\), there exist maps \(i_c:V_c\to V_a\otimes V_b\), \(p_c:V_a\otimes V_b\to V_c\), for all natural \(c\), satisfying \(i_c;p_c=\mathrm{id}_{V_c}\) on admissible \(c\le a+b\), and \(\sum_c p_c;i_c=\mathrm{id}_{V_a\otimes V_b}\) over that finite range. These maps need not be the chosen trivalent maps.
--   * \(D_n;C_n=\iota(\Delta(n))\,\mathrm{id}_{\mathbf1}\).
--
--   Here \(f;g\) means first \(f\), then \(g\). The notation \(\star\) inserts the canonical associators and unitors for composition and never exchanges strands. Tensor factors have exactly their displayed order; \(A\triangleleft f\) and \(f\triangleright A\) mean left and right whiskering.
--
--   Choose covectors \(t_{abc}:V_a\otimes V_b\otimes V_c\to\mathbf1\) for every natural triple. Their cup-bent forms are defined exactly by
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
--   Thus \(s_l^{ab}:V_l\to V_a\otimes V_b\), \(f_{ab}^{l}:V_a\otimes V_b\to V_l\), and \(t^{abc}:\mathbf1\to V_a\otimes V_b\otimes V_c\). In particular the covector used in \(t^{abc}\) has reversed labels \(c,b,a\); this is not complex conjugation.
--
--   There are exactly two vertex-normalization assumptions:
--   \[
--   t^{abc};t_{abc}=\iota(\theta(a,b,c))\,\mathrm{id}_{\mathbf1},
--   \qquad R(t_{abc})=t_{bca},
--   \]
--   where
--   \[
--   R(t_{abc})=\mathrm{id}\star(D_a\triangleright(V_b\otimes V_c\otimes V_a))
--   \star(V_a\triangleleft(t_{abc}\triangleright V_a))\star C_a.
--   \]
--
--   Define the ordered four-leg states and covectors
--   \[
--   \begin{aligned}
--   X_{abcd;l}&=D_l\star(s_l^{ab}\otimes s_l^{cd})\star\mathrm{id},\\
--   H_{abcd;j}&=t^{ajd}\star(V_a\triangleleft(s_j^{bc}\triangleright V_d))\star\mathrm{id},\\
--   H^R_{abcd;j}&=\mathrm{id}\star(V_a\triangleleft(f_{bc}^{j}\triangleright V_d))\star t_{ajd}.
--   \end{aligned}
--   \]
--   The states have outputs \(a,b,c,d\), in that order. For signed \(j,l\), define
--   \[
--   T(a,b,c,d;j,l)=\begin{cases}X_{adcb;j};H^R_{adcb;l}&j,l\ge0,\\0&\text{otherwise}.\end{cases}
--   \]
--   The boundary permutation is \(a,d,c,b\), and the last channel \(l\) is the inner rung. In addition to category axioms and vertex normalization, assume the separate seed
--   \[
--   T(a,b,c,d;j,2)=\iota(\mathcal T(a,b,c,d;j,2))\,\mathrm{id}_{\mathbf1}
--   \quad(a,b,c,d,j\in\mathbb N).
--   \]
--   This evaluates only the already-defined tetrahedral networks with last channel 2. It neither assumes the closure identifications below nor assumes a full all-channel scalar evaluation.
--
--   ## Scalar quantities, including the seed
--
--   An integer triple is admissible when its entries are nonnegative, satisfy every triangle inequality, and have even sum. Write \(\operatorname{Had}(a,b,c,d;j)\) for admissibility of both \((a,d,j)\) and \((b,c,j)\). Define
--   \[
--   [n]=\frac{q^n-q^{-n}}{q-q^{-1}},\quad
--   [n]!=\begin{cases}0&n<0,\\\prod_{r=1}^n[r]&n\ge0,\end{cases}\quad
--   \Delta(n)=\begin{cases}(-1)^n[n+1]&n\ge0,\\0&n<0.\end{cases}
--   \]
--   For admissible \((a,b,c)\), with \(s=(a+b+c)/2\), set
--   \[
--   \theta(a,b,c)=(-1)^s\frac{[s+1]![s-a]![s-b]![s-c]!}{[a]![b]![c]!};
--   \]
--   otherwise set it to zero. Set
--   \[
--   h_j=\begin{cases}\theta(a,d,j)\theta(b,c,j)/\Delta(j)&\operatorname{Had}(a,b,c,d;j),\\0&\text{otherwise},\end{cases}
--   \]
--   and, on admissible \((a,b,l)\),
--   \[
--   \lambda_{ab}(l)=\frac{[(a-b+l)/2][(-a+b+l)/2]-[(a+b-l)/2][(a+b+l)/2+2]}{[2]},
--   \]
--   with value zero otherwise. The last bracket is \([(a+b+l)/2+2]\), not a half with the 2 inside its numerator.
--
--   For the seed define
--   \[
--   A=\left(\frac{a+d+j}{2},\frac{b+c+j}{2},\frac{a+b+l}{2},\frac{c+d+l}{2}\right),\quad
--   B=\left(\frac{b+d+j+l}{2},\frac{a+c+j+l}{2},\frac{a+b+c+d}{2}\right).
--   \]
--   When \((a,d,j),(b,c,j),(a,b,l),(c,d,l)\) are all admissible,
--   \[
--   \mathcal T(a,b,c,d;j,l)=
--   \frac{\prod_{i=1}^4\prod_{r=1}^3[B_r-A_i]!}{[a]![b]![c]![d]![j]![l]!}
--   \sum_{z=0}^{a+b+c+d+j+l}
--   \frac{(-1)^z[z+1]!}{\prod_{i=1}^4[z-A_i]!\prod_{r=1}^3[B_r-z]!};
--   \]
--   it is zero otherwise. Halves are integer divisions, exact on the admissible branch.
--
--   ## The operator and five asserted conclusions
--
--   The operator acts on the first two boundary legs, without exchanging them:
--   \[
--   K_{ab}=\iota([a][b])\,
--   \bigl((s_a^{a2}\triangleright V_b)\star(V_a\triangleleft f_{2b}^{b})\bigr),\qquad
--   \widehat K_{abcd}=\mathrm{id}\star(K_{ab}\triangleright(V_c\otimes V_d))\star\mathrm{id}.
--   \]
--   The rung is split from \(a\) and fused into \(b\). Write
--   \(M_{jk}=H_{abcd;k};\widehat K_{abcd};H^R_{abcd;j}\). Thus \(k\) is the input-state channel and \(j\) the final covector channel. All labels in the following five conclusions range over the natural numbers, with no extra admissibility or nonvanishing hypotheses except the explicit premise in item 4.
--
--   1. The first literal four-vertex closure is identified with a tetrahedron:
--      \[
--      t^{akd}\star(s_a^{a2}\triangleright(V_k\otimes V_d))
--      \star(V_a\triangleleft(f_{2k}^{j}\triangleright V_d))\star t_{ajd}
--      =T(a,a,k,j;d,2).
--      \]
--      There is no factor \([a][b]\) in this closure identity. Its right side expands to \(X_{ajka;d};H^R_{ajka;2}\): the first channel is \(d\), not \(j\) or \(k\).
--   2. Define a morphism \(Q:V_2\otimes V_k\to V_j\) by
--      \[
--      Q=\bigl((V_2\triangleleft s_k^{bc})\star(f_{2b}^{b}\triangleright V_c)\bigr);f_{bc}^{j}.
--      \]
--      Then the second literal closure satisfies
--      \[
--      D_j;\bigl((s_j^{2k};Q)\triangleright V_j\bigr);C_j
--      =T(b,b,k,j;c,2).
--      \]
--      Its right side is \(X_{bjkb;c};H^R_{bjkb;2}\), with first channel \(c\). Again there is no scalar prefactor.
--   3. The complete matrix entry factors as
--      \[
--      M_{jk}=\frac{\iota([a][b])}{\iota(\theta(2,k,j))}
--      \bigl(T(a,a,k,j;d,2);T(b,b,k,j;c,2)\bigr).
--      \]
--      The two tetrahedra are endomorphisms of \(\mathbf1\), composed in exactly the displayed order. The denominator is \(\theta(2,k,j)\), not an external-channel norm or a square root.
--   4. If \((2,k,j)\) is not admissible, then \(M_{jk}=0\).
--   5. The same entry has the explicit numerical value
--      \[
--      M_{jk}=\iota(L_{jk})\,\mathrm{id}_{\mathbf1},
--      \]
--      where the independent scalar definition is
--      \[
--      L_{jk}=\begin{cases}
--      -h_j[2]\lambda_{aj}(d)\lambda_{bj}(c)/([j][j+2])
--        &j=k,\ \operatorname{Had}(a,b,c,d;j),\ j\ne0,\\
--      h_n[(a+d-m)/2][(b+c-m)/2]
--        &|j-k|=2,\ m=\min(j,k),\ n=\max(j,k),\
--         \operatorname{Had}(a,b,c,d;m),\operatorname{Had}(a,b,c,d;n),\\
--      0&\text{otherwise}.
--      \end{cases}
--      \]
--      In particular \(L_{00}=0\), even when horizontal channel 0 is admissible. The neighboring entries use the norm at the larger channel \(n\), not the smaller one. They are symmetric under \(j\leftrightarrow k\), and zero off the diagonal and step-2 neighbors. There is no normalization by \(h_j\) in the matrix-entry conclusion itself.
--
--   The two literal closure identifications in items 1 and 2 are conclusions to establish. They are not supplied as conditional inputs, and they do not follow merely by substituting a name into the seed. The seed assumes scalar evaluations of the canonical right-hand tetrahedra; identification of the literal left-hand composites with those networks remains part of what is asserted. The five statements are conjoined, not a chain of implications adding earlier statements as hypotheses. No rung-eigenvalue theorem, recurrence, basis-completeness statement, or all-channel tetrahedral evaluation is assumed.
--
--   ## Total division and the central-channel-zero clause
--
--   Every scalar quotient is a total field quotient: \(0^{-1}=0\), so \(x/0=0\). In particular item 3 is asserted even when \(\theta(2,k,j)=0\); it is not restricted to the admissible central channel and carries no hidden denominator-nonzero premise. Since \(\theta\) is defined to be zero on inadmissible triples, its right-hand side then vanishes under total division. Item 4 expressly asserts that the categorical left-hand side vanishes too. Although item 3 together with the zero extension implies that same equality, item 4 remains an explicit conjunct; cancellation by the central theta is not a valid proof of this case. For natural \(j,k\), central admissibility allows precisely step-2 neighboring channels and equal positive channels; \((2,0,0)\) is inadmissible. Its zero case is therefore relevant to the exceptional diagonal entry.
--
--   The signed factorial zeros likewise cause invalid summands to vanish through total division, not through an implicit nonzero-denominator condition. These rational-function conventions make no claim about specialization at complex poles or roots of unity. The five identities are the asserted statement; no proof of them is supplied here.
-- source:
--   I. Khavkine, Recurrence relation for the 6j-symbol of su_q(2) as a symmetric eigenvalue problem, International Journal of Geometric Methods in Modern Physics (2015), https://doi.org/10.1142/S0219887815501170; https://arxiv.org/abs/1009.2261. Eqs. (16)–(20), tetrahedral factorization and symmetric tridiagonal matrix entries.

import Definitions.Def_QuantumSixJNetwork

open CategoryTheory MonoidalCategory
open scoped BigOperators QuantumSixJ

universe v u

namespace QuantumSixJ.Network

theorem matrix_entries {C : Type u} [Category.{v} C] [Preadditive C] [Linear K C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear K C]
    (S : SuQ2Data C) (W : Vertex S) (hS : SuQ2Axioms S) (hW : VertexNormalized W) (hSeed : TetSeed W) :
    (∀ a d j k : ℕ,
      (W.vertexUp a k d ⊗≫ (W.split a a 2 ▷ (S.V k ⊗ S.V d)) ⊗≫
        (S.V a ◁ (W.fuse 2 k j ▷ S.V d)) ⊗≫ W.vertex a j d) =
          W.tet a a k j d 2) ∧
    (∀ b c j k : ℕ,
      let q : S.V 2 ⊗ S.V k ⟶ S.V j :=
        (S.V 2 ◁ W.split k b c) ⊗≫ (W.fuse 2 b b ▷ S.V c) ≫ W.fuse b c j
      (S.cup j ≫ ((W.split j 2 k ≫ q) ▷ S.V j) ≫ S.cap j) =
        W.tet b b k j c 2) ∧
    (∀ a b c d j k : ℕ,
      W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
        (ι (⟬(a : ℤ)⟭ * ⟬(b : ℤ)⟭) / ι (θ (2 : ℤ) k j)) •
          (W.tet a a k j d 2 ≫ W.tet b b k j c 2)) ∧
    (∀ a b c d j k : ℕ, ¬ Admissible (2 : ℤ) k j →
      W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j = 0) ∧
    (∀ a b c d j k : ℕ,
      W.H a b c d k ≫ W.Kop a b c d ≫ W.Hcov a b c d j =
        ι (L a b c d j k) • 𝟙 (𝟙_ C)) := by sorry

end QuantumSixJ.Network
