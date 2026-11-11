-- Prove2me | Theorems.Thm_PartialHomog_Threshold_lemma_E_13
-- name    : PartialHomog.Threshold.lemma_E_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:28:07.358465+00:00
-- url     : https://prove2.me/theorems/2e4a1c4c-1d80-47c4-b02d-d52ef32ad1e9
-- title:
--   Lemma E.13 — one spare gate: with $\dim\operatorname{span}\{q_i^{[\ge2]}\} \le K+1$, every product gate multiplies exactly two affine functions
-- statement:
--   Let $\phi=(\phi_0,\dots,\phi_{K-1})$ be a real quadratic map in $z=(z_0,\dots,z_{N-1})$ whose $K$ coordinates are linearly independent quadratic forms, and whose span $W$ contains no nonzero product of two linear forms and contains a form of rank at least $4$. Let $\Phi$ be a division-free circuit over $\mathbb R$ computing $\phi$ with product gates of unbounded fan-in, none of them removable, and let $V=\operatorname{span}\{\hat q^{[\ge2]}: q\text{ a product gate}\}$. Suppose
--   $$\dim V=\dim\operatorname{span}\{\hat q_i^{[\ge2]}\}\le K+1$$
--   (for example, $\Phi$ has at most $K+1$ product gates). Then every product gate of $\Phi$ has exactly two non-constant inputs, both affine (inputs counted with multiplicity; all other inputs are constants).
--
--   This is the core of the paper's threshold result: one product gate beyond the number of outputs does not let cancellation of higher-degree terms help.
--
--   Differences from the source:
--   - encoding: a circuit is a directed acyclic graph; product gates q_1, …, q_M in a topological order; unordered inputs of a product gate counted with multiplicity → a straight-line program `Circuit R N K`: gate t reads only gates < t, a product gate is a list of ≥ 2 earlier gate indices, product gates ordered by gate number; reason: every DAG has a topological order and a list with repeats is a multiset of inputs; the same circuits, the same polynomials and the same product-gate counts
--   - encoding: indices 1, …, K and variables z_1, …, z_N → `Fin K` and `Fin N` (0-based); reason: relabelling only
--   - encoding: polynomials in R[z] → formal polynomials `MvPolynomial (Fin N) R`; 'computes' is equality of polynomials; reason: the paper's polynomials are formal (§A.1)
--   - encoding: rank of a real quadratic form → `quadRank`: rank of the matrix of second formal partial derivatives (2S for f = zᵀSz); reason: rank 2S = rank S; standard rank
--   - encoding: W contains no nonzero product of two linear forms → ∀ ℓ m linear forms, ℓ * m ∈ W → ℓ * m = 0; reason: literal
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 26 (PDF 28), Lemma E.13

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit
import Definitions.Def_PartialHomog_Threshold_ProductGates
import Definitions.Def_PartialHomog_Threshold_QuadRank

open MvPolynomial

namespace PartialHomog.Threshold

/-- Lemma E.13 (One spare gate), p. 26. Let `ϕ` be a real quadratic map whose `K` coordinates
are linearly independent quadratic forms, whose span `W` contains no nonzero product of two
linear forms and contains a form of rank at least 4. Let `Φ` be a division-free circuit over `ℝ`
computing `ϕ` with product gates of unbounded fan-in, none removable, such that
`dim span{q̂^{[≥2]}} ≤ K + 1`. Then every product gate has exactly two non-constant inputs (with
multiplicity), both affine. -/
theorem lemma_E_13 {N K : ℕ}
    (ϕ : Fin K → MvPolynomial (Fin N) ℝ) (hquad : IsQuadraticMap ϕ)
    (hli : LinearIndependent ℝ ϕ)
    (hnoprod : ∀ ℓ m : MvPolynomial (Fin N) ℝ, IsLinearForm ℓ → IsLinearForm m →
      ℓ * m ∈ spanW ϕ → ℓ * m = 0)
    (hrank : ∃ f ∈ spanW ϕ, 4 ≤ quadRank f)
    (Φ : Circuit ℝ N K) (hΦ : Φ.Computes ϕ) (hrem : ∀ v, ¬ Φ.IsRemovable v)
    (hdim : Module.finrank ℝ Φ.spanV ≤ K + 1) :
    ∀ v, Φ.IsProdGate v → Φ.MultipliesTwoAffine v := by sorry

end PartialHomog.Threshold
