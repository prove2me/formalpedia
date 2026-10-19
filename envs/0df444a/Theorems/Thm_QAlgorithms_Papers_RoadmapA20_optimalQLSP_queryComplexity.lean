-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapA20_optimalQLSP_queryComplexity
-- name    : QAlgorithms.Papers.RoadmapA20.optimalQLSP_queryComplexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:45:46.714047+00:00
-- url     : https://prove2.me/theorems/28dc2e71-a70f-4985-8052-d54d360e58e4
-- title:
--   Optimal sparse-access quantum linear systems query complexity
-- statement:
--   Consider the quantum linear systems problem for an invertible, complex, $d$-sparse $N\times N$ matrix $A$, with $1\le d\le N$, $\|A\|\le1$, and $\|A^{-1}\|\le\kappa$, where these are operator norms and $\kappa$ is known. For a nonzero vector $b$, a supplied preparation circuit prepares $|b\rangle=b/\|b\|$. The solver must output a success flag of probability at least $1/2$ and, conditioned on success, a normalized reduced density matrix within trace distance $\epsilon$ of $|x\rangle\langle x|$, where $|x\rangle=A^{-1}b/\|A^{-1}b\|$. Both $A$ and $A^\dagger$ have reversible row-location and XOR entry-value oracles; the $d$ locations listed in each row are distinct, cover all nonzeros, and may include zeros. Only matrix-oracle calls count, including inverse and controlled calls. Supplied preparation operations and known quantum operations are free.
--
--   Let $Q(d,\kappa,\epsilon)$ be the supremum over positive dimensions $N\ge d$ and public finite exact entry encodings of the least natural worst-case matrix-query budget of a solver correct for every compatible promised input and oracle completion. Solvers are chosen before the hidden matrix, vector, and oracle completions. Empty sets of feasible budgets and unbounded suprema retain $+\infty$. There exist absolute constants $c,C>0$, $\kappa_0\ge1$, $d_0\ge1$, and $0<\epsilon_0<1$ such that, for every $\kappa\ge\kappa_0$, $d\ge d_0$, and $0<\epsilon\le\epsilon_0$,
--
--   $$
--   c\kappa\sqrt d\log(1/\epsilon)\le Q(d,\kappa,\epsilon)\le C\kappa\sqrt d\log(1/\epsilon).
--   $$
--
--   This gives matching upper and worst-case lower bounds jointly in sparsity, inverse-norm bound, and precision. The constants and thresholds are independent of dimension, encoding, and input.
--
--   **Formalization Note** Complexity is represented in $\mathbb R_{\ge0}\cup\{+\infty\}$ using the frozen `OptimalQLSP.queryComplexity`. General matrices and general positive dimensions are retained; the Hermitian reduction and power-of-two registers used inside the proof do not restrict the headline.
-- source:
--   An Optimal Quantum Linear Systems Algorithm, arXiv:2609.35660v1, Theorem 1, equation (6), PDF p. 2. https://arxiv.org/abs/2609.35660v1 . PDF SHA-256: 82b1de042691486cb046682596d61a6d657f0a7498494a6653b217d5088ce38d.

import Definitions.Def_QAlgorithms_Defs_OptimalQLSPComplexity
set_option autoImplicit false

namespace QAlgorithms.Papers.RoadmapA20

/-- Theorem 1, equation (6), arXiv:2609.35660v1, PDF page 2:
the QLSP has query complexity Theta(kappa * sqrt(d) * log(1/eps)).

The frozen complexity ranges over positive dimensions N >= d and finite exact
entry encodings. For each public dimension and encoding, a solver is chosen before
every hidden invertible d-sparse complex A, nonzero b, and compatible oracle completion.
The input promises are specNorm A <= 1 and specNorm A inverse <= kappa. Both A and
its adjoint have row-location and XOR value access; matrix calls, their inverses and
controlled versions are counted, while supplied state preparation and known operations
are free. Successful reduced output may be mixed: success probability is at least 1/2
and its normalized conditional state has trace distance at most eps from the normalized
solution. Universal thresholds express the multiparameter asymptotic convention on p.2.

Source audit: p.9 equation (37) is read as a lower bound on recovery probability,
as its proof requires; the exact probability is norm(u)^2 / (norm(QT u)^2 + norm(u)^2).
No correction to Theorem 1 is needed.
-/
theorem optimalQLSP_queryComplexity :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ kappa0 : ℝ, 1 ≤ kappa0 ∧
      ∃ d0 : ℕ, 1 ≤ d0 ∧
      ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 < 1 ∧
      ∀ kappa : ℝ, ∀ hkappa : 1 ≤ kappa, kappa0 ≤ kappa →
      ∀ d : ℕ, ∀ hd : 1 ≤ d, d0 ≤ d →
      ∀ eps : ℝ, ∀ heps : 0 < eps ∧ eps < 1, eps ≤ eps0 →
        ENNReal.ofReal (c * kappa * Real.sqrt (d : ℝ) * Real.log (1 / eps)) ≤
          OptimalQLSP.queryComplexity d hd kappa eps hkappa heps ∧
        OptimalQLSP.queryComplexity d hd kappa eps hkappa heps ≤
          ENNReal.ofReal (C * kappa * Real.sqrt (d : ℝ) * Real.log (1 / eps)) := by sorry

end QAlgorithms.Papers.RoadmapA20
