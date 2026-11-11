-- Prove2me | Theorems.Thm_PartialHomog_Threshold_sec_1_3_K_le_Cinf_le_C2
-- name    : PartialHomog.Threshold.sec_1_3_K_le_Cinf_le_C2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:28:21.696815+00:00
-- url     : https://prove2.me/theorems/62dae8e5-c13c-4897-9e1e-93694203ed3d
-- title:
--   §1.3 — $K \le C_\infty(\phi) \le C_2(\phi)$ for a quadratic map with $K$ linearly independent coordinates
-- statement:
--   Let $F$ be a field and $\phi=(\phi_0,\dots,\phi_{K-1})$ a quadratic map in $z=(z_0,\dots,z_{N-1})$ over $F$ whose $K$ coordinates are linearly independent. Then
--   $$K\le C_\infty(\phi)\le C_2(\phi),$$
--   where $C_2(\phi)$ is the least number of products of linear forms in a quadratic algorithm for $\phi$ and $C_\infty(\phi)$ the least number of product gates of a division-free circuit over $F$ with product gates of unbounded fan-in computing $\phi$.
--
--   These are the trivial bounds between which Corollary E.14 locates $C_\infty$.
--
--   Differences from the source:
--   - encoding: indices 1, …, K and variables z_1, …, z_N → `Fin K` and `Fin N` (0-based); reason: relabelling only
--   - generalization: ϕ real (the setting of Corollary E.14); the §1.3 sentence names no field → any field F; reason: at F = ℝ it is the source's statement
--   - reading: §1.3 defines C2 as the least number of product gates of a division-free fan-in-two circuit, 'the least number of products of linear forms in a quadratic algorithm [Str73]', and C∞ 'when the fan-in is unbounded' → C2 = least number of products in a quadratic algorithm; C∞ over division-free circuits with any fan-in ≥ 2; reason: the paper states the two C2 definitions agree and uses the quadratic-algorithm one in §E.2; 'when the fan-in is unbounded' changes only the fan-in of the division-free circuits, as §E.2's definition of C∞ confirms
--   - encoding: circuits are directed acyclic graphs → straight-line programs `Circuit F N K` (gate t reads only gates < t; a product gate is a list of ≥ 2 earlier gate indices, inputs with multiplicity); reason: every DAG has a topological order; the same circuits and the same product-gate counts
--   - encoding: polynomials → formal polynomials `MvPolynomial (Fin N) F`; 'computes' is equality of polynomials; reason: the paper's polynomials are formal (§A.1)
--   - encoding: 'least number' C2, C∞ → `sInf` of a subset of ℕ; reason: both sets are nonempty for a quadratic map, so sInf is the minimum
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 4 (PDF 6), §1.3

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit
import Definitions.Def_PartialHomog_Threshold_Complexity

open MvPolynomial

namespace PartialHomog.Threshold

/-- §1.3 (p. 4): for a quadratic map `ϕ` over a field `F` with `K` linearly independent
coordinates, `K ≤ C∞(ϕ) ≤ C₂(ϕ)`. -/
theorem sec_1_3_K_le_Cinf_le_C2 {F : Type*} [Field F] {N K : ℕ}
    (ϕ : Fin K → MvPolynomial (Fin N) F) (hquad : IsQuadraticMap ϕ)
    (hli : LinearIndependent F ϕ) :
    K ≤ Cinf ϕ ∧ Cinf ϕ ≤ C2 ϕ := by sorry

end PartialHomog.Threshold
