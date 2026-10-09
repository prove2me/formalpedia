-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_preserving_isolated_section_points
-- name    : PhilipponMultiplicity.exists_principal_open_preserving_isolated_section_points
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-04T21:42:54.743312+00:00
-- url     : https://prove2.me/theorems/2a246e47-34c6-4f2c-a0fb-a5aa936f6df2
-- title:
--   A principal-open family preserving isolated mixed-section point counts
-- statement:
--   Let $K$ be a Philippon base field, let $M=\prod_i\mathbf P^{n_i}$ be the mission's finite multiprojective space, and let $W\subseteq M$ be closed and irreducible. Choose integers $0\leq\alpha_i\leq n_i$ with $\sum_i\alpha_i=\dim W$, and vector subspaces $L_i\subseteq K^{n_i+1}$ of codimension $\alpha_i$. Let $S$ be a finite set of points of $Z=W\cap\prod_i\mathbf P(L_i)$, each having a Zariski-open neighborhood whose intersection with $Z$ lies in $S$.
--
--   Fix any ordered block list $l=(i_0,\ldots,i_{s-1})$ containing each $i$ exactly $\alpha_i$ times. For a coefficient matrix $c$, put
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   Z(c)=\{x\in W:P_j(c)(x)=0\text{ for every }j<s\}.
--   $$
--   There is a nonzero polynomial $F$ in the coefficient entries such that
--   $$
--   F(c)\ne0\quad\Longrightarrow\quad\text{there is an injection of sets }S\hookrightarrow Z(c).
--   $$
--   Thus a nonempty principal-open family of mixed equations preserves the number of prescribed isolated points. The original section may have positive-dimensional components away from $S$. The injection need not retain the original points or be a morphism. Empty $S$ and zero-length lists are allowed. No smoothness, finiteness of $Z(c)$, associated-prime avoidance, or local-ring regularity is asserted.
--
--   **Formalization Note.** This auxiliary coefficient-space persistence statement remains Open. The coefficient matrix includes entries from every projective block, but the form in row $j$ uses only block $i_j$. The conclusion concerns an injection of point sets and carries no assertion about local rings. It is separate from the existing smooth-family frontier.
--
--   A checked reduction now constructs a coefficient array for every prescribed linear section, with surjective block matrices and exactly the original kernels in the specified row order. It transfers the inclusion and isolation conditions through the exact equality of zero sets, then extracts a principal open from an open neighborhood of the initial coefficient point. The remaining [open-neighborhood persistence theorem](https://prove2.me/theorems/e3f679bb-787a-4101-af01-b03541b77c95) is a geometric assertion about equation fibers and stays Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the general mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . Stacks Project, Lemma 37.41.5 (Tag 02LO), etale localization separating finitely many isolated fibre points, https://stacks.math.columbia.edu/tag/02LO ; Lemma 37.74.2 (Tag 0F32), universal openness of locally quasi-finite morphisms over a geometrically unibranch locally Noetherian base when every component dominates, https://stacks.math.columbia.edu/tag/0F32 ; Lemma 29.29.4 (Tag 02FZ), openness of the zero-dimensional fibre locus, https://stacks.math.columbia.edu/tag/02FZ . Auxiliary synthesis, not a verbatim source assertion: the incidence variety over the irreducible W is a vector bundle of dimension equal to coefficient-space dimension. An isolated special fibre point forces dominance. On the quasi-finite locus use universal openness and etale separation of the prescribed points to obtain a nonempty open where their number persists, then take a principal open. The incidence comparison, dimension and dominance arguments, and all descent to the concrete point model remain proof obligations of this child.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_preserving_isolated_section_points
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
      (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) →
      ∀ S : Set M.Point, S.Finite → S ⊆ linearSlice M W L →
      (∀ x ∈ S, ∃ U : Set M.Point, @IsOpen _ M.zariskiTopology U ∧ x ∈ U ∧
        U ∩ linearSlice M W L ⊆ S) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by sorry

end PhilipponMultiplicity
