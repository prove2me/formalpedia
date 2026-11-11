-- Prove2me | Theorems.Thm_PartialHomog_Threshold_corollary_B_2
-- name    : PartialHomog.Threshold.corollary_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:27:29.773574+00:00
-- url     : https://prove2.me/theorems/de0034f9-4ecd-4fa2-bd15-35cbbc17405a
-- title:
--   Corollary B.2 — degree-two structure: linear parts propagate linearly; every gate is a combination of product gates plus an affine function
-- statement:
--   Let $\Phi$ be a division-free arithmetic circuit over a commutative ring $R$ in variables $z$, with product gates listed in a topological order (here: by gate number).
--
--   1. For a sum gate $v$ with $\hat v=\sum_u\lambda_u\hat u$, $\hat v^{[1]}=\sum_u\lambda_u\hat u^{[1]}$. For a product gate $v$ with inputs $u_1,\dots,u_s$ (with multiplicity),
--   $$\hat v^{[1]}=\sum_{j=1}^{s}\Big(\prod_{l\ne j}\hat u_l^{[0]}\Big)\hat u_j^{[1]},\qquad \hat u_l^{[0]}\in R ,$$
--   in particular $\hat v^{[1]}$ is an $R$-linear combination of the $\hat u^{[1]}$ for the inputs $u$ of $v$.
--   2. Every gate $v$ computes $\hat v=\sum_q\lambda_{v,q}\hat q+a_v$, the sum over product gates $q$, with $\lambda_{v,q}\in R$, $a_v$ of degree at most $1$, and $\lambda_{v,q}=0$ unless $q=v$ or $q$ is a predecessor of $v$. Hence $\hat v^{[k]}=\sum_q\lambda_{v,q}\hat q^{[k]}$ for every $k\ge2$, and if $q$ has inputs $u_1,\dots,u_s$ then $\hat u_j^{[\ge2]}\in\operatorname{span}_R\{\hat q'^{[\ge 2]}: q'\text{ a product gate before }q\}$.
--
--   This is the degree-two case of the paper's partial homogenization (Proposition B.1): above degree one only product gates create new information. It gives $W\subseteq V$ in Lemma E.13 and Corollary E.14.
--
--   **Formalization Note** $\hat u^{[0]}$ is `constantCoeff`; coefficients $\lambda_{v,\cdot}$ are a function `lam : Fin Φ.size → R` vanishing off the product gates that equal $v$ or precede it.
--
--   Differences from the source:
--   - encoding: a circuit is a directed acyclic graph; product gates q_1, …, q_M in a topological order; unordered inputs of a product gate counted with multiplicity → a straight-line program `Circuit R N K`: gate t reads only gates < t, a product gate is a list of ≥ 2 earlier gate indices, product gates ordered by gate number; reason: every DAG has a topological order and a list with repeats is a multiset of inputs; the same circuits, the same polynomials and the same product-gate counts
--   - encoding: polynomials in R[z] → formal polynomials `MvPolynomial (Fin N) R`; 'computes' is equality of polynomials; reason: the paper's polynomials are formal (§A.1)
--   - encoding: variables z_1, …, z_N, children u_1, …, u_s and coefficients λ_{v,i} indexed by i = 1, …, M → `Fin N`, input-list positions `Fin (Φ.prodInputs v).length`, and `lam : Fin Φ.size → R` indexed by gate number and vanishing off the product gates; reason: relabelling only
-- source:
--   Spiizer, Partial Homogenization and the Structure of Optimal Algebraic Algorithms, STOC 2027 submission (manuscript sha256 33096d05…), p. 17 (PDF 19), Corollary B.2

import Mathlib
import Definitions.Def_PartialHomog_Threshold_Components
import Definitions.Def_PartialHomog_Threshold_Circuit

open MvPolynomial

namespace PartialHomog.Threshold

/-- Corollary B.2 (Degree two structure), p. 17. For a division-free circuit `Φ` over a
commutative ring `R`, whose product gates are listed in gate order (a topological order):
(1) degree-one parts propagate linearly through sum gates, and through a product gate with
inputs `u_1, …, u_s` by `v̂^{[1]} = ∑_j (∏_{l ≠ j} û_l^{[0]}) û_j^{[1]}`; in particular it lies in the
span of the inputs' degree-one parts; (2) every gate computes `∑_q λ_{v,q} q̂ + a_v` with `a_v` of
degree at most one, `λ_{v,q} = 0` unless `q` is a product gate equal to `v` or a predecessor of
`v`, hence `v̂^{[k]} = ∑_q λ_{v,q} q̂^{[k]}` for all `k ≥ 2`; and the part of degree at least two
of every input of a product gate `q` lies in the span of the parts `q̂'^{[≥2]}` of the product
gates `q' < q`. -/
theorem corollary_B_2 {R : Type*} [CommRing R] {N K : ℕ} (Φ : Circuit R N K) :
    (∀ v : Fin Φ.size, ∀ terms : List (R × Fin v.val), Φ.gate v = Gate.sum terms →
      homogeneousComponent 1 (Φ.value v) =
        (terms.map fun e =>
          e.1 • homogeneousComponent 1 (Φ.value ⟨e.2.val, lt_trans e.2.isLt v.isLt⟩)).sum) ∧
    (∀ v : Fin Φ.size, Φ.IsProdGate v →
      homogeneousComponent 1 (Φ.value v) =
        ∑ j : Fin (Φ.prodInputs v).length,
          C (∏ l ∈ Finset.univ.erase j, constantCoeff (Φ.value (Φ.prodInputs v)[l])) *
            homogeneousComponent 1 (Φ.value (Φ.prodInputs v)[j])) ∧
    (∀ v : Fin Φ.size, Φ.IsProdGate v →
      homogeneousComponent 1 (Φ.value v) ∈
        Submodule.span R
          ((fun u => homogeneousComponent 1 (Φ.value u)) '' {u | u ∈ Φ.prodInputs v})) ∧
    (∀ v : Fin Φ.size, ∃ lam : Fin Φ.size → R,
      (∀ q, lam q ≠ 0 → Φ.IsProdGate q ∧ (q = v ∨ Φ.IsPredecessor q v)) ∧
      (Φ.value v - ∑ q ∈ Φ.prodGates, lam q • Φ.value q).totalDegree ≤ 1 ∧
      ∀ k : ℕ, 2 ≤ k →
        homogeneousComponent k (Φ.value v) =
          ∑ q ∈ Φ.prodGates, lam q • homogeneousComponent k (Φ.value q)) ∧
    (∀ q : Fin Φ.size, Φ.IsProdGate q → ∀ u ∈ Φ.prodInputs q,
      partGe 2 (Φ.value u) ∈
        Submodule.span R
          ((fun q' => partGe 2 (Φ.value q')) '' {q' | Φ.IsProdGate q' ∧ q' < q})) := by sorry

end PartialHomog.Threshold
