-- Prove2me | Theorems.Thm_PlanarDFVSKernel_lemma_3_5
-- name    : PlanarDFVSKernel.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:51.037438+00:00
-- url     : https://prove2.me/theorems/89d38bab-ef4e-499c-8e06-bd2c801a1cba
-- title:
--   Lemma 3.5 — $\mu(x,y)\le \mathrm{cc}(G-\{x,y\})+m_{xy}\le k+2$
-- statement:
--   **Lemma 3.5.** Let $D$ be a plane digraph in which Reduction Rules 1 to 3 have been exhaustively applied: Rules 1 and 2 are no longer applicable (no loops, no repeated arcs with the same direction, every weakly connected component strongly connected, at least two distinct in- and out-neighbours everywhere), and for distinct $x,y$ in one strongly connected component $D_0$ the digraph $D_0-\{x,y\}$ has at most $k$ weakly connected components. Then every pair of distinct vertices $x,y$ in one component satisfies
--   $$\mu(x,y)\ \le\ \mathrm{cc}(G-\{x,y\})+m_{xy}\ \le\ k+2,$$
--   where $\mu(x,y)$ is the number of faces whose boundaries contain both $x$ and $y$, $G$ is the underlying undirected multigraph of the component, and $m_{xy}$ is the number of edges joining $x$ and $y$.
--
--   The bound controls how many faces two vertices can share; it is the input to Reduction Rule 4.
--
--   Differences from the source:
--   - generalization: a planar input after Reduction Rules 1 to 3 have been exhaustively applied → a drawing of any digraph with the four reduced properties of Rules 1–2 and with cc(D₀ − {x, y}) ≤ k for distinct x, y in one strongly connected component D₀ (Rule 3 inapplicable); no Rule 1 (iii)/(iv) budget outcomes; reason: the proof uses only these properties; every exhaustively reduced instance satisfies them
--   - encoding: faces counted in the induced embedding of each strongly connected component, including its outer face → dart orbits of the drawing of the whole digraph; reason: orbits of a rotation system stay in one connected component and each component has its own outer orbit; the weakly connected components are the strongly connected ones
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.5, p.11 (PDF 12)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs
import Definitions.Def_PlanarDFVSKernel_ReducedRules12
import Definitions.Def_PlanarDFVSKernel_ccDel
import Definitions.Def_PlanarDFVSKernel_mxy
import Definitions.Def_PlanarDFVSKernel_mu

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp

/-- **Lemma 3.5** (Sheng, Xiao, *A Polynomial Kernel for Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), Lemma 3.5, p.11 (PDF 12)): "After Reduction Rules 1 to 3 have been
exhaustively applied, every pair of distinct vertices x, y in a component satisfies
µ(x, y) ≤ cc(G − {x, y}) + m_xy ≤ k + 2."

Let `D` be a plane digraph in which Reduction Rules 1 and 2 are no longer applicable and Reduction
Rule 3 is not applicable (`cc(D′ − {x, y}) ≤ k` for distinct `x, y` in one strongly connected
component `D′`). Then for distinct `x, y` in one strongly connected component, the number of faces
containing both is at most `cc(G − {x, y}) + m_xy`, and this is at most `k + 2`.

**Formalization Note** Faces are the published dart orbits of the drawing `E`, which are the faces
of the induced embedding of each strongly connected component taken separately (the weakly connected
components are the strongly connected ones). -/
theorem lemma_3_5 {n m : ℕ} {G : Graph n m} (E : Drawing G) (k : ℕ) (hred : ReducedRules12 G)
    (hR3 : ∀ x y : Fin n, x ≠ y → SameSCC G x y → ccDel G x y ≤ k) :
    ∀ x y : Fin n, x ≠ y → SameSCC G x y →
      mu E x y ≤ ccDel G x y + mxy G x y ∧ ccDel G x y + mxy G x y ≤ k + 2 := by sorry

end PlanarDFVSKernel
