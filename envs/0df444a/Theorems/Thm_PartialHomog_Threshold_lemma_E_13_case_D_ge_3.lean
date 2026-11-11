-- Prove2me | Theorems.Thm_PartialHomog_Threshold_lemma_E_13_case_D_ge_3
-- name    : PartialHomog.Threshold.lemma_E_13_case_D_ge_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:28:06.784452+00:00
-- url     : https://prove2.me/theorems/645f87c0-5422-47e8-bb6c-5652bb0bb9b7
-- title:
--   Proof of Lemma E.13, case $D \ge 3$ — all product gates have degree $D$, affine inputs, and a common factorization $\kappa_i\prod_j(c_{ij}+\ell_j)$
-- statement:
--   Let $\phi=(\phi_0,\dots,\phi_{K-1})$ be a real quadratic map in $z=(z_0,\dots,z_{N-1})$ whose $K$ coordinates are linearly independent quadratic forms, and whose span $W$ contains no nonzero product of two linear forms and contains a form of rank at least $4$. Let $\Phi$ be a division-free circuit over $\mathbb R$ computing $\phi$ with product gates of unbounded fan-in, none of them removable, and let $V=\operatorname{span}\{\hat q^{[\ge2]}: q\text{ a product gate}\}$. Suppose $\dim V=K+1$, let $q_1$ be the first product gate in the topological order and $D\ge3$ its degree. Then every element of $V\setminus W$ has degree $D$, every product gate has degree $D$, every input of every product gate is affine, and there are linear forms $\ell_1,\dots,\ell_D$ such that every product gate $q_i$ computes, for some $\kappa_i\ne0$ and reals $c_{i1},\dots,c_{iD}$,
--   $$q_i=\kappa_i\prod_{j=1}^{D}(c_{ij}+\ell_j),\qquad q_i^{[k]}=\kappa_iE_k(c_i),\qquad E_k(c_i)=\sum_{|T|=k}\Big(\prod_{j\notin T}c_{ij}\Big)\prod_{j\in T}\ell_j .$$
--
--   This is the structural step after which the proof of Lemma E.13 reaches a contradiction; so its hypotheses are never all satisfied (Lemma E.13 shows $D=2$). It is a waypoint of the proof, stated with the full context in which the paper asserts it.
--
--   **Formalization Note** "First in topological order" is the product gate of least gate number; $D$ is its total degree, passed as `D` with `hD_def`. Linear parts "up to scalars and order" are absorbed into $\kappa_i$ and $c_{ij}$ (products commute).
--
--   Differences from the source:
--   - encoding: a circuit is a directed acyclic graph; product gates q_1, …, q_M in a topological order; unordered inputs of a product gate counted with multiplicity → a straight-line program `Circuit R N K`: gate t reads only gates < t, a product gate is a list of ≥ 2 earlier gate indices, product gates ordered by gate number; reason: every DAG has a topological order and a list with repeats is a multiset of inputs; the same circuits, the same polynomials and the same product-gate counts
--   - encoding: indices 1, …, K and variables z_1, …, z_N → `Fin K` and `Fin N` (0-based); reason: relabelling only
--   - encoding: polynomials in R[z] → formal polynomials `MvPolynomial (Fin N) R`; 'computes' is equality of polynomials; reason: the paper's polynomials are formal (§A.1)
--   - encoding: rank of a real quadratic form → `quadRank`: rank of the matrix of second formal partial derivatives (2S for f = zᵀSz); reason: rank 2S = rank S; standard rank
--   - encoding: W contains no nonzero product of two linear forms → ∀ ℓ m linear forms, ℓ * m ∈ W → ℓ * m = 0; reason: literal
--   - encoding: indices j = 1, …, D and the subsets T ⊆ {1, …, D} → `Fin D` and `Finset (Fin D)`; reason: relabelling only
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 27 (PDF 29), proof of Lemma E.13, Case D ≥ 3

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit
import Definitions.Def_PartialHomog_Threshold_ProductGates
import Definitions.Def_PartialHomog_Threshold_QuadRank

open MvPolynomial

namespace PartialHomog.Threshold

/-- Proof of Lemma E.13 (p. 27), case `D ≥ 3`: under the hypotheses of Lemma E.13 with
`dim V = K + 1`, if the first product gate `q₁` (least gate number) has degree `D ≥ 3`, then every
element of `V \ W` and every product gate has degree `D`, every input of every product gate is
affine, and there are linear forms `ℓ_1, …, ℓ_D` such that every product gate computes
`κ_q ∏_j (c_{qj} + ℓ_j)` with `κ_q ≠ 0`, so that `q̂^{[k]} = κ_q E_k(c_q)`,
`E_k(c) = ∑_{|T| = k} (∏_{j ∉ T} c_j) ∏_{j ∈ T} ℓ_j`. -/
theorem lemma_E_13_case_D_ge_3 {N K : ℕ}
    (ϕ : Fin K → MvPolynomial (Fin N) ℝ) (hquad : IsQuadraticMap ϕ)
    (hli : LinearIndependent ℝ ϕ)
    (hnoprod : ∀ ℓ m : MvPolynomial (Fin N) ℝ, IsLinearForm ℓ → IsLinearForm m →
      ℓ * m ∈ spanW ϕ → ℓ * m = 0)
    (hrank : ∃ f ∈ spanW ϕ, 4 ≤ quadRank f)
    (Φ : Circuit ℝ N K) (hΦ : Φ.Computes ϕ) (hrem : ∀ v, ¬ Φ.IsRemovable v)
    (hdim : Module.finrank ℝ Φ.spanV = K + 1)
    (q₁ : Fin Φ.size) (hq₁ : Φ.IsProdGate q₁) (hfirst : ∀ q, Φ.IsProdGate q → q₁ ≤ q)
    (D : ℕ) (hD_def : (Φ.value q₁).totalDegree = D) (hD : 3 ≤ D) :
    (∀ P ∈ Φ.spanV, P ∉ spanW ϕ → P.totalDegree = D) ∧
    (∀ q, Φ.IsProdGate q → (Φ.value q).totalDegree = D) ∧
    (∀ q, Φ.IsProdGate q → ∀ u ∈ Φ.prodInputs q, IsAffine (Φ.value u)) ∧
    ∃ ℓ : Fin D → MvPolynomial (Fin N) ℝ, (∀ j, IsLinearForm (ℓ j)) ∧
      ∀ q, Φ.IsProdGate q → ∃ κ : ℝ, κ ≠ 0 ∧ ∃ c : Fin D → ℝ,
        Φ.value q = C κ * ∏ j, (C (c j) + ℓ j) ∧
        ∀ k : ℕ, homogeneousComponent k (Φ.value q) =
          C κ * ∑ T ∈ (Finset.univ : Finset (Finset (Fin D))).filter (fun T => T.card = k),
            (∏ j ∈ Tᶜ, C (c j)) * ∏ j ∈ T, ℓ j := by sorry

end PartialHomog.Threshold
