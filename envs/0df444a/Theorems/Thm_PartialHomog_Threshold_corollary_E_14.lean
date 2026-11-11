-- Prove2me | Theorems.Thm_PartialHomog_Threshold_corollary_E_14
-- name    : PartialHomog.Threshold.corollary_E_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:28:16.454582+00:00
-- url     : https://prove2.me/theorems/a1371b25-beca-4231-b80b-397819bcfd7d
-- title:
--   Corollary E.14 — $C_\infty(\phi) \ge \min\{C_2(\phi), K+2\}$, and $C_\infty(\phi) = C_2(\phi)$ whenever $C_2(\phi) \le K+2$
-- statement:
--   Let $\phi=(\phi_0,\dots,\phi_{K-1})$ be a real quadratic map in $z=(z_0,\dots,z_{N-1})$ whose $K$ coordinates are linearly independent quadratic forms, and whose span $W$ contains no nonzero product of two linear forms and contains a form of rank at least $4$. Let $C_2(\phi)$ be the least number of products in a quadratic algorithm for $\phi$, and $C_\infty(\phi)$ the least number of product gates in a division-free circuit over $\mathbb R$ with product gates of unbounded fan-in computing $\phi$. Then
--   $$C_\infty(\phi)\ge\min\{C_2(\phi),\,K+2\},$$
--   and in particular $C_\infty(\phi)=C_2(\phi)$ whenever $C_2(\phi)\le K+2$.
--
--   Below the threshold $K+2$, product gates of unbounded fan-in (with nesting, constants and any depth) save nothing over products of two linear forms.
--
--   Differences from the source:
--   - encoding: indices 1, …, K and variables z_1, …, z_N → `Fin K` and `Fin N` (0-based); reason: relabelling only
--   - encoding: polynomials in R[z] → formal polynomials `MvPolynomial (Fin N) R`; 'computes' is equality of polynomials; reason: the paper's polynomials are formal (§A.1)
--   - encoding: rank of a real quadratic form → `quadRank`: rank of the matrix of second formal partial derivatives (2S for f = zᵀSz); reason: rank 2S = rank S; standard rank
--   - encoding: W contains no nonzero product of two linear forms → ∀ ℓ m linear forms, ℓ * m ∈ W → ℓ * m = 0; reason: literal
--   - encoding: C∞: division-free circuits (directed acyclic graphs) with product gates of unbounded fan-in → `Cinf` over straight-line programs `Circuit ℝ N K` with product gates of fan-in ≥ 2; reason: every DAG has a topological order; the same circuits and counts
--   - encoding: 'least number' C2, C∞ → `sInf` of a subset of ℕ; reason: both sets are nonempty for a quadratic map, so sInf is the minimum
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 28 (PDF 30), Corollary E.14 (hypotheses of Lemma E.13, p. 26 (PDF 28); definitions of C2, C∞, p. 27 (PDF 29))

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_QuadRank
import Definitions.Def_PartialHomog_Threshold_Complexity

open MvPolynomial

namespace PartialHomog.Threshold

/-- Corollary E.14, p. 28. Let `ϕ` be a real quadratic map whose `K` coordinates are linearly
independent quadratic forms, whose span `W` contains no nonzero product of two linear forms and
contains a form of rank at least 4. Then `C∞(ϕ) ≥ min{C₂(ϕ), K + 2}`, and `C∞(ϕ) = C₂(ϕ)`
whenever `C₂(ϕ) ≤ K + 2`. Here `C∞` is taken over division-free circuits over `ℝ` with product
gates of any fan-in at least two, and `C₂` is the least number of products in a quadratic
algorithm. -/
theorem corollary_E_14 {N K : ℕ}
    (ϕ : Fin K → MvPolynomial (Fin N) ℝ) (hquad : IsQuadraticMap ϕ)
    (hli : LinearIndependent ℝ ϕ)
    (hnoprod : ∀ ℓ m : MvPolynomial (Fin N) ℝ, IsLinearForm ℓ → IsLinearForm m →
      ℓ * m ∈ spanW ϕ → ℓ * m = 0)
    (hrank : ∃ f ∈ spanW ϕ, 4 ≤ quadRank f) :
    min (C2 ϕ) (K + 2) ≤ Cinf ϕ ∧ (C2 ϕ ≤ K + 2 → Cinf ϕ = C2 ϕ) := by sorry

end PartialHomog.Threshold
