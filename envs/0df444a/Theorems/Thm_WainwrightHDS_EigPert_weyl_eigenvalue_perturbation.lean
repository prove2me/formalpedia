-- Prove2me | Theorems.Thm_WainwrightHDS_EigPert_weyl_eigenvalue_perturbation
-- name    : WainwrightHDS.EigPert.weyl_eigenvalue_perturbation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:27:11.868494+00:00
-- url     : https://prove2.me/theorems/3a96f3b0-7364-496a-bdce-dd885359ce12
-- title:
--   Eq. (8.9) — Weyl's inequality $\max_j |\gamma_j(Q) - \gamma_j(R)| \le |||Q - R|||_2$
-- statement:
--   Let $Q$ and $R$ be real symmetric $d \times d$ matrices, with eigenvalues $\gamma_1(\cdot) \ge \dots \ge \gamma_d(\cdot)$ in non-increasing order. Then
--
--   $$
--   \max_{j = 1, \dots, d} \bigl|\gamma_j(Q) - \gamma_j(R)\bigr| \;\le\; |||Q - R|||_2 ,
--   $$
--
--   where $|||\cdot|||_2$ is the $\ell_2$ operator norm.
--
--   Eigenvalues are thus stable under symmetric perturbations: the $j$-th eigenvalue moves by at most the operator norm of the perturbation. In the proof of Theorem 8.5 this guarantees that the perturbed matrix $\widehat\Sigma = \Sigma + P$ keeps a positive eigengap when $|||P|||_2 < \nu/2$.
--
--   **Formalization Note** The maximum over $j$ is written as a statement for every index $j$; indices are 0-based.
--
--   Differences from the source:
--   - encoding: max over j = 1, …, d → `∀ j : Fin d` (0-based); reason: a bound on the maximum is a bound for every j; same instances
--   - encoding: symmetric matrices Q, R → `IsHermitian` over ℝ; reason: for real matrices Hermitian means symmetric; same instances
-- source:
--   Wainwright, High-Dimensional Statistics, Cambridge University Press 2019, Section 8.1.2, p. 241 (PDF p. 261), Eq. (8.9) (proof asked in Exercise 8.3)

import Mathlib
import Definitions.Def_WainwrightHDS_EigPert_opNorm2
import Definitions.Def_WainwrightHDS_EigPert_gamma

namespace WainwrightHDS.EigPert

/-- **Weyl's inequality for eigenvalues, Eq. (8.9).**
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University
Press 2019, Section 8.1.2, p. 241 (PDF p. 261), Eq. (8.9) (proof asked in Exercise 8.3):
for symmetric matrices `Q` and `R`, "`max_{j=1,…,d} |γ_j(Q) − γ_j(R)| ≤ |||Q − R|||₂`".

For symmetric `d × d` matrices `Q`, `R` and every index `j`, the `j`-th largest eigenvalues differ
by at most the ℓ₂ operator norm of `Q − R`.

**Formalization Note.** The `max` over `j` is written as a `∀ j`; indices are 0-based. -/
theorem weyl_eigenvalue_perturbation {d : ℕ} (Q R : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) :
    ∀ j : Fin d, |gamma Q hQ j - gamma R hR j| ≤ opNorm2 (Q - R) := by sorry

end WainwrightHDS.EigPert
