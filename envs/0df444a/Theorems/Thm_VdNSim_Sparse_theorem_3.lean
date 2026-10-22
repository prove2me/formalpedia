-- Prove2me | Theorems.Thm_VdNSim_Sparse_theorem_3
-- name    : VdNSim.Sparse.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:02.961995+00:00
-- url     : https://prove2.me/theorems/52e524ad-de02-40ca-8435-f2ee7b87b254
-- title:
--   Theorem 3, p. 11 — sparse matrix-element estimation by sampling
-- statement:
--   Let $\psi$ and $\phi$ be normalized states on a finite computational basis, and let $A$ be an $s$-sparse operator of spectral norm at most one, represented by column data $(\alpha_i,r_i)$. From $K\ge1$ independent samples of $p_x=|\psi_x|^2$ and $K$ independent samples of $q_y=|\phi_y|^2$, form the paper's estimator $\widehat m$ from the sample means of $F_i$ and $G_i$. For every $\varepsilon>0$,
--
--   $$\Pr\{|\widehat m-\langle\phi|A|\psi\rangle|>\varepsilon\}\le8s\exp\!\left(-\frac{K\varepsilon^2}{32s^4}\right).$$
--
--   This is the quantitative accuracy statement underlying the paper's classical approximation of a sparse matrix element.
--
--   **Formalization Note** The paper states polynomial accuracy and an efficient algorithm; the displayed tail follows from its Eq. (18) and the bounds on $F_i$ and $G_i$. Running time is outside the model. A single sample pair is shared across all $i$; the argument applies without independence between the $i$-summands. The case $s=0$ is interpreted using Lean's total division, and then both the estimator and target vanish.
-- source:
--   Van den Nest, Simulating quantum computers with probabilistic methods, arXiv:0911.1624v3, p. 11, Theorem 3; pp. 12–13, proof; p. 23, Eq. (18)

import Mathlib
import Definitions.Def_VdNSim_Sparse_Model

noncomputable section

namespace VdNSim.Sparse

/-- Theorem 3, p. 11, with the sampling estimator and tail derived in its proof. -/
theorem theorem_3 {X : Type*} [Fintype X] [DecidableEq X]
    {s K : ℕ} (hK : 0 < K)
    (ψ ϕ : X → ℂ) (hψ : ∑ x, prob ψ x = 1) (hϕ : ∑ y, prob ϕ y = 1)
    (A : Matrix X X ℂ) (hsp : IsSparse s A)
    (hA : QAlgorithms.specNorm A ≤ 1) (D : ColumnData A s)
    {ε : ℝ} (hε : 0 < ε) :
    failProb ψ ϕ D K (matElem ϕ A ψ) ε ≤
      8 * (s : ℝ) * Real.exp (-((K : ℝ) * ε ^ 2) / (32 * (s : ℝ) ^ 4)) := by sorry

end VdNSim.Sparse
