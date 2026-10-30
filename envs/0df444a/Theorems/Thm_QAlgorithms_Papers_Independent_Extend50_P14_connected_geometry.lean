-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_connected_geometry
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.connected_geometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:53:55.865102+00:00
-- url     : https://prove2.me/theorems/3990c469-3f61-48f2-a85d-ffd35e95987f
-- title:
--   Connected geometry preserves the generated group
-- statement:
--   Let n identical positive-dimensional sites carry the same on-site unitary representation u of a group G. Let a connected graph describe their geometry and let 2≤k≤n. Write V_k for finite products of symmetric gates supported on at most k sites, and V_{k,graph} for the corresponding products with each support inducing a connected subgraph. Then
--
--   $$V_{k,\mathrm{graph}}=V_k.$$
--
--   Thus the specified geometric restriction preserves exact reachability.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 2, I.A: connected geometry does not change the generated group

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.2, I.A: identical on-site actions are essential for symmetric SWAPs.
The proof's range k≥2 is made explicit. -/
theorem connected_geometry {G A : Type*} [Group G] [Fintype A] [DecidableEq A]
    [Nonempty A] (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (r : OnSite G (fun _ : Fin n => A))
    (hSame : ∀ i j g, r.u i g = r.u j g)
    (graph : SimpleGraph (Fin n)) (hConnected : graph.Connected) :
    geometricGroup r.total graph k = symmetricLocalGroup r.total k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
