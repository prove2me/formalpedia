-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P35_tangency_not_sufficient
-- name    : QAlgorithms.Papers.Independent.Support50.P35.tangency_not_sufficient
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:38:49.290915+00:00
-- url     : https://prove2.me/theorems/011685bc-db93-4462-9c7b-907c325e01c9
-- title:
--   Multiple tangency need not imply support
-- statement:
--   There exists a genuine affine hyperplane \(H=\{q:a\cdot q=b\}\) bitangent to the compact irreducible nonsingular real variety
--
--   $$
--   M=\{(x,y,z):x^2+y^2=1,\ z=x^3\}
--   $$
--
--   at \((0,1,0)\) and \((0,-1,0)\), while \(M\) contains a point with \(a\cdot q<b\) and a point with \(a\cdot q>b\). Thus neither halfspace bounded by \(H\) contains \(M\). This gives a concrete instance of the source's assertion that multiple tangency alone is insufficient for support.
-- source:
--   Convex Hulls of Varieties and Entanglement Measures Based on the Roof Construction, arXiv:quant-ph/0402055v2, PDF p. 7, Remark 2.7: multiple tangency need not imply support

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P35

noncomputable section

open scoped Matrix ComplexConjugate Topology Manifold

namespace QAlgorithms.Papers.Independent.Support50.P35

/-- PDF p.7, Remark 2.7: explicit witness to failure of the converse;
the graph of x^3 has bitangent plane z=0 but lies on both sides of it. -/
theorem tangency_not_sufficient :
    ∃ H : Hyperplane 3, IsCompact cubicGraph ∧ IsNonsingularVariety cubicGraph ∧
      IsMTangent H cubicGraph (![![0, 1, 0], ![0, -1, 0]]) ∧
      (∃ y ∈ cubicGraph, normalMap H.normal y < H.offset) ∧
      (∃ y ∈ cubicGraph, H.offset < normalMap H.normal y) := by sorry

end QAlgorithms.Papers.Independent.Support50.P35

end
