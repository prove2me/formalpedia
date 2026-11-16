-- Prove2me | Theorems.Thm_PlantedIQP_Supplement_theorem_60
-- name    : PlantedIQP.Supplement.theorem_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:06:13.38031+00:00
-- url     : https://prove2.me/theorems/925b79ab-0a62-4d18-bba7-f7b039dfa2ed
-- title:
--   Theorem 60 — $\mathrm{symSR}(P)\le r$ iff a formally independent space of dimension $\ge n-r$
-- statement:
--   **Theorem 60.** Let $F$ be any field and let $P\in F[x_1,\dots,x_n]$ be a cubic form, i.e. a polynomial homogeneous of degree $3$. For every $r\in\mathbb N$,
--
--   $$
--   \mathrm{symSR}(P)\le r\iff P \text{ has a formally independent space } V\le F^n \text{ with } \dim V\ge n-r .
--   $$
--
--   Here $\mathrm{symSR}(P)\le r$ means that $P=\sum_{i=1}^{s}\ell_iQ_i$ with $s\le r$, linear forms $\ell_i$ and quadratic forms $Q_i$ (Definition 57). $V$ is formally independent if substituting a parametrization $x=\sum_jt_jb_j$ of $V$ into $P$ gives the zero polynomial.
--
--   The theorem identifies symmetric slice rank, which Remark 59 shows equals the strength of $P$, with the codimension of the largest formally independent space. Section 4 uses this link to transfer the NP-hardness of slice rank to the independent space problem.
--
--   **Formalization Note** Polynomials are formal (`MvPolynomial`), so over $\mathbb F_2$ the form need not be multilinear.
--
--   Differences from the source:
--   - encoding: plugging the equations of the subspace into P → every substitution x ↦ Σ_j t_j b_j with b_1, …, b_d ∈ V sends P to the zero polynomial; reason: equivalent to the substitution for one basis of V, since every family in V is a linear image of a basis
--   - encoding: dimension ≥ n − r (an integer) → n − r in ℕ (truncated); reason: dimensions are nonnegative, so the two readings agree for every r
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Theorem 60, p.31 (Definition 57, p.30; formal independence, p.31)

import Mathlib
import Definitions.Def_PlantedIQP_Supplement_SymSliceRank

set_option autoImplicit false

namespace PlantedIQP.Supplement

/-- **Theorem 60** (Bläser, Gullans, Hangleiter, Liu, Qiao, arXiv:2609.39918, sha256 6e261694…,
Theorem 60, p.31). "For any cubic form P, symSR(P) ≤ r iff P has a formally independent space of
dimension ≥ n − r."

**Formalization Note.** Over every field `F` (Section 4, p.28). A cubic form is a formal polynomial
`P ∈ F[x_1, …, x_n]` homogeneous of degree 3 (`MvPolynomial (Fin n) F`). `symSR(P) ≤ r` is
`SymSliceRankLE P r`; "formally independent" (p.31) is `IsFormallyIndependent`: substituting the
parametrization of the subspace into `P` gives the zero polynomial. `n − r` is natural-number
subtraction, which agrees with the integer reading because dimensions are nonnegative. -/
theorem theorem_60 {F : Type*} [Field F] {n : ℕ} (P : MvPolynomial (Fin n) F)
    (hP : P.IsHomogeneous 3) (r : ℕ) :
    SymSliceRankLE P r ↔
      ∃ V : Submodule F (Fin n → F), IsFormallyIndependent P V ∧ n - r ≤ Module.finrank F V := by sorry

end PlantedIQP.Supplement
