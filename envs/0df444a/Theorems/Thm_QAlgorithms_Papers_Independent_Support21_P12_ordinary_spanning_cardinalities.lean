-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P12_ordinary_spanning_cardinalities
-- name    : QAlgorithms.Papers.Independent.Support21.P12.ordinary_spanning_cardinalities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:12:33.020038+00:00
-- url     : https://prove2.me/theorems/25464fce-a05a-4c3f-85b9-57e0932eabea
-- title:
--   Spanning cardinalities for semi-admissible ordinary BMW algebras
-- statement:
--   Let $S$ be an integral domain with ordinary BMW unit parameters satisfying (2.1), and suppose the whole left ideal $W_{2,S,r}e_1$ is torsion free. Assume Assumption 5.3 for $0<d<r$, including d-semi-admissibility and the annihilator $p_0(T)=\prod_{i=1}^d(T-u_i)$. For $n\ge2$, write $J_n=W_ne_{n-1}W_n$ and let $b'(n)$ be the number of Brauer diagrams on n strands with a horizontal edge. There are spanning sets of cardinalities
--
--   $$d^n b'(n)\text{ for }J_n,\qquad d^n b'(n)+r^n n!\text{ for }W_n.$$
--
--   Here $W_n$ is the actual cyclotomic quotient. These are spanning-set claims; linear independence is not assumed or asserted.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, PDF p. 13, Lemma 5.8

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Lemma 5.8, PDF pp.13--14: the two cardinality conclusions, with n≥2
for the named contraction. No basis conclusion is inserted here. -/
theorem ordinary_spanning_cardinalities (S : Type*) [CommRing S] [IsDomain S]
    (omega : ℕ → S) (rho q : Sˣ) (hcompat : (↑(rho⁻¹) : S) - ↑rho =
      ((↑(q⁻¹) : S) - ↑q) * (omega 0 - 1)) (r : ℕ) (u : Fin r → S)
    (d : ℕ) (h : d ≤ r)
    (hu : ValidRoots (.ordinary rho q hcompat) u)
    (htor : IdealTorsionFree S omega (.ordinary rho q hcompat) r u)
    (hsplit : SplitSemi S omega (.ordinary rho q hcompat) r u d h)
    (n : ℕ) (hn : 2 ≤ n) :
    let K : Kind S omega := .ordinary rho q hcompat
    HasSpanningSetCard (contractionIdeal (S := S) (ce S omega K r u n (n-2)))
      (d ^ n * horizontalDiagramCount n) ∧
    HasSpanningSetCard (⊤ : Submodule S (Cyclotomic S omega K r u n))
      (d ^ n * horizontalDiagramCount n + r ^ n * n.factorial) := by sorry

end QAlgorithms.Papers.Independent.Support21.P12

end
