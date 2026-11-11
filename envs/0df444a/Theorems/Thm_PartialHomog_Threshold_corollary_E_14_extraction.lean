-- Prove2me | Theorems.Thm_PartialHomog_Threshold_corollary_E_14_extraction
-- name    : PartialHomog.Threshold.corollary_E_14_extraction
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:28:30.368199+00:00
-- url     : https://prove2.me/theorems/24948c32-9322-4039-8d07-5085186ed32f
-- title:
--   Proof of Corollary E.14 — a circuit whose product gates multiply two affine functions yields a quadratic algorithm with as many products
-- statement:
--   Let $\phi=(\phi_0,\dots,\phi_{K-1})$ be a quadratic map over a commutative ring $R$ and $\Phi$ a division-free circuit over $R$ computing $\phi$ in which every product gate multiplies two affine functions (exactly two non-constant inputs, both affine). Then the parts of degree $2$ of the outputs are combinations of the products of the linear parts of these functions: $\phi$ has a quadratic algorithm with as many products as $\Phi$ has product gates; in particular
--   $$C_2(\phi)\le\#\{\text{product gates of }\Phi\}.$$
--
--   With Lemma E.13 this gives $C_2(\phi)\le C_\infty(\phi)$ when $C_\infty(\phi)\le K+1$.
--
--   Differences from the source:
--   - encoding: a circuit is a directed acyclic graph; product gates q_1, …, q_M in a topological order; unordered inputs of a product gate counted with multiplicity → a straight-line program `Circuit R N K`: gate t reads only gates < t, a product gate is a list of ≥ 2 earlier gate indices, product gates ordered by gate number; reason: every DAG has a topological order and a list with repeats is a multiset of inputs; the same circuits, the same polynomials and the same product-gate counts
--   - encoding: indices 1, …, K and variables z_1, …, z_N → `Fin K` and `Fin N` (0-based); reason: relabelling only
--   - encoding: polynomials in R[z] → formal polynomials `MvPolynomial (Fin N) R`; 'computes' is equality of polynomials; reason: the paper's polynomials are formal (§A.1)
--   - generalization: the circuit of Corollary E.14: over ℝ, ϕ satisfying the hypotheses of Lemma E.13, C∞(ϕ) product gates → any commutative ring R, any quadratic map ϕ, any circuit computing ϕ whose product gates multiply two affine functions; reason: the extraction uses only Corollary B.2 and the shape of the product gates; the source's case is R = ℝ with the circuit of Corollary E.14
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 28 (PDF 30), proof of Corollary E.14

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit
import Definitions.Def_PartialHomog_Threshold_ProductGates
import Definitions.Def_PartialHomog_Threshold_Complexity

open MvPolynomial

namespace PartialHomog.Threshold

/-- Proof of Corollary E.14 (p. 28), extraction of a quadratic algorithm: if every product gate of
a division-free circuit `Φ` computing a quadratic map `ϕ` multiplies two affine functions (exactly
two non-constant inputs, both affine), then `ϕ` has a quadratic algorithm with as many products
as `Φ` has product gates. -/
theorem corollary_E_14_extraction {R : Type*} [CommRing R] {N K : ℕ}
    (ϕ : Fin K → MvPolynomial (Fin N) R) (hquad : IsQuadraticMap ϕ)
    (Φ : Circuit R N K) (hΦ : Φ.Computes ϕ)
    (htwo : ∀ v, Φ.IsProdGate v → Φ.MultipliesTwoAffine v) :
    HasQuadAlg ϕ Φ.numProd := by sorry

end PartialHomog.Threshold
