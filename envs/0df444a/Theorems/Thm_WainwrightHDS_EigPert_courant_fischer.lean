-- Prove2me | Theorems.Thm_WainwrightHDS_EigPert_courant_fischer
-- name    : WainwrightHDS.EigPert.courant_fischer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T00:26:43.002416+00:00
-- url     : https://prove2.me/theorems/99313cb1-d489-4106-a143-26c2951a304e
-- title:
--   Exercise 8.1 — Courant–Fischer variational representation of $\gamma_j(Q)$
-- statement:
--   Let $Q$ be a real symmetric $d \times d$ matrix and let $j \in \{2, \dots, d\}$. Let $\mathcal{V}_{j-1}$ be the collection of all linear subspaces $\mathbb{V} \subseteq \mathbb{R}^d$ of dimension $j - 1$, and $\mathbb{V}^\perp$ the orthogonal complement of $\mathbb{V}$. Then the $j$-th largest eigenvalue of $Q$ is
--
--   $$
--   \gamma_j(Q) \;=\; \min_{\mathbb{V} \in \mathcal{V}_{j-1}} \ \max_{u \in \mathbb{V}^\perp \cap \mathbb{S}^{d-1}} \langle u, Qu\rangle ,
--   $$
--
--   where both the minimum and the maximum are attained.
--
--   This min–max characterization is the tool the book suggests for proving Weyl's inequality (8.9) (Exercise 8.3), which in turn controls the eigengap of the perturbed matrix in Theorem 8.5.
--
--   **Formalization Note** The statement says that $\gamma_j(Q)$ is the least element of the set of values $c$ for which some subspace $\mathbb{V}$ of dimension $j-1$ makes $c$ the greatest value of $\langle u, Qu\rangle$ over unit vectors $u \in \mathbb{V}^\perp$ (`IsLeast` / `IsGreatest`, so attainment is part of the claim).
--
--   Differences from the source:
--   - encoding: j ∈ {2, …, d}, γ_j, subspaces of dimension j − 1 → `j : Fin d` with `1 ≤ j.val`, `gamma Q hQ j`, `finrank V = j.val`; reason: Lean indices are 0-based, the book's j is `j.val + 1`; same instances
--   - encoding: symmetric matrix Q → `Q.IsHermitian` over ℝ; reason: for real matrices Hermitian means Qᵀ = Q; same instances
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, p. 256 (PDF p. 276), Exercise 8.1, Eq. (8.41)

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_gamma

namespace WainwrightHDS.EigPert

/-- **Exercise 8.1 (Courant–Fischer variational representation), Eq. (8.41).**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, p. 256 (PDF p. 276), Exercise 8.1:
"For a given integer `j ∈ {2, …, d}`, let `𝒱_{j−1}` denote the collection of all subspaces of
dimension `j−1`. For any symmetric matrix `Q`, show that the `j`th largest eigenvalue is given by
`γ_j(Q) = min_{V ∈ 𝒱_{j−1}} max_{u ∈ V^⊥ ∩ S^{d−1}} ⟨u, Qu⟩`."

For a symmetric `Q` and a 0-based index `j` with `1 ≤ j` (the book's `j + 1 ∈ {2, …, d}`), the
value `gamma Q hQ j` is the least element of the set of numbers `c` such that, for some subspace
`V` of dimension `j`, `c` is the greatest value of `⟨u, Qu⟩` over unit vectors `u ∈ V^⊥`.

**Formalization Note.** Index base: the book's `γ_j` with `j ∈ {2, …, d}` is `gamma Q hQ j'`
with `j' = j − 1 ∈ {1, …, d − 1}`, and the subspaces have dimension `j' = j − 1`. Both "min" and
"max" are stated as attained (`IsLeast`, `IsGreatest`). -/
theorem courant_fischer {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsHermitian)
    (j : Fin d) (hj : 1 ≤ j.val) :
    IsLeast
      {c : ℝ | ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin d)), Module.finrank ℝ V = j.val ∧
        IsGreatest ((fun u => inner ℝ u (Matrix.toEuclideanLin Q u)) ''
          {u | u ∈ Vᗮ ∧ ‖u‖ = 1}) c}
      (gamma Q hQ j) := by sorry

end WainwrightHDS.EigPert
