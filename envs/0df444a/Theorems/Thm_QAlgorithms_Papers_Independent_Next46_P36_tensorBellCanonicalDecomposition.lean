-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P36_tensorBellCanonicalDecomposition
-- name    : QAlgorithms.Papers.Independent.Next46.P36.tensorBellCanonicalDecomposition
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:43:55.896216+00:00
-- url     : https://prove2.me/theorems/62f68126-6ea8-4d81-a5e1-d807a8d06a20
-- title:
--   Lemma 4: actual tensor-Bell input and canonical embedding
-- statement:
--   Let $d\ge1$ and $N\ge1$. On the fixed product basis, let $U^{\otimes N}$ be the actual tensor-power representation of $SU(d)$, and let $B$ be an exhaustive unitary Clebsch–Gordan basis for its positive-multiplicity inequivalent irreducible blocks. Set $c_\mu=\sqrt{d_\mu m_\mu/d^N}$, where $m_\mu$ belongs to $U^{\otimes N}$.
--
--   Regroup the $N$ Bell pairs into registers $A,B$. Define $J$ from this very basis by
--
--   $$J_{(a,b),(\mu,i,j)}=\frac1{\sqrt{m_\mu}}\sum_{k=1}^{m_\mu}B_{a,(\mu,i,k)}\overline{B_{b,(\mu,j,k)}}.$$
--
--   Then $J^\dagger J=I$, $((U_g^{\otimes N})\otimes I)J=JU_g^{\rm can}$ for every $g$, $\sum_\mu c_\mu^2=1$, and the normalized supplied input satisfies
--
--   $$\frac{\operatorname{vec}(I_{d^N})}{\sqrt{d^N}}=J\left(\bigoplus_\mu\frac{c_\mu}{\sqrt{d_\mu}}\operatorname{vec}(I_\mu)\right).$$
--
--   The embedding and bases are independent of the unknown transformation. This ties the canonical orbit to the physical Bell input rather than an unrelated abstract memory.
-- source:
--   Optimal estimation of group transformations using entanglement, arXiv:quant-ph/0506267v2, PDF p. 9, Lemma 4; Appendix Eqs. (75)-(76)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P36

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P36

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P36.matrixMeasurable

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- PDF pp.9-11 Lemma 4 and Eqs.(59),(60),(75),(76): the embedding is the
specific one computed from the actual Clebsch-Gordan basis; it is fixed before g. -/
theorem tensorBellCanonicalDecomposition
    (d N : ℕ) (hd : 0 < d) (hN : 1 ≤ N)
    {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (D : S → BasedIrrep (Matrix.specialUnitaryGroup (Fin d) ℂ)) (hD : OccurringIrrepsInequivalent D)
    (B : BasedDecomposition (actualTensorRepresentation d N) D) :
    QAlgorithms.IsState (tensorBell d N) ∧
    (∑ s, (bellCoefficient D B s) ^ 2) = 1 ∧
    (bellEmbedding D B)ᴴ * bellEmbedding D B = 1 ∧
    (∀ g, bellAction d N g * bellEmbedding D B =
      bellEmbedding D B * canonicalAction D g) ∧
    tensorBell d N = WithLp.toLp 2 ((bellEmbedding D B).mulVec
      (WithLp.ofLp (canonicalInput D (fun s => (bellCoefficient D B s : ℂ)) (fun _ => 1)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P36

end
