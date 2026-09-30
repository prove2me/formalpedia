-- Prove2me | Theorems.Thm_SolodovSvaiterVI_Alg21_lemma2_2_proj_xbar_eq
-- name    : SolodovSvaiterVI.Alg21.lemma2_2_proj_xbar_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T10:32:47.664721+00:00
-- url     : https://prove2.me/theorems/a1d2107e-ed6d-4048-8b3e-89ef5bfa9155
-- title:
--   Lemma 2.2 — $P_{C \cap H_i}[\bar x^i] = P_{C \cap H_i}[x^i]$ with $\bar x^i = P_{H_i}[x^i]$
-- statement:
--   Let $C$ be a closed convex subset of $\mathbb{R}^n$ and $F : \mathbb{R}^n \to \mathbb{R}^n$ continuous. Assume that the solution set $S$ of $\mathrm{VI}(F, C)$ is nonempty and that condition (1.2) holds, and let $\gamma, \sigma \in (0,1)$. Let $x \in C$ with $r(x) \ne 0$, and let $k$ be a nonnegative integer satisfying the linesearch condition (2.1) at $x$. Put
--
--   $$z = x - \gamma^k r(x), \qquad H = \{y \in \mathbb{R}^n \mid \langle F(z), y - z\rangle \le 0\}, \qquad \bar x = P_H[x].$$
--
--   Then
--
--   $$P_{C \cap H}[\bar x] = P_{C \cap H}[x].$$
--
--   In the notation of Algorithm 2.1 ($x = x^i$, $k = k_i$, $H = H_i$), this is $x^{i+1} = P_{C\cap H_i}[\bar x^i]$: the next iterate may be computed by first projecting onto the halfspace and then onto $C \cap H_i$. This is the geometric fact behind the Fejér-type inequality (2.6).
--
--   **Formalization Note** One step of the algorithm is stated for a generic point $x$ and a generic $k$ satisfying (2.1); the paper's hypothesis "the linesearch procedure (2.1) is well defined" becomes this assumption on $k$ (minimality is not needed). Projections are `projOnto`; under the hypotheses $C \cap H$ and $H$ are nonempty closed convex sets, so these are true projections. Continuity of $F$ and $\sigma < 1$ are standing assumptions of the paper, not used by this step.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 768, Lemma 2.2

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_SolodovSvaiterVI_Alg21_SatisfiesCond12
import Definitions.Def_SolodovSvaiterVI_Alg21_residual
import Definitions.Def_SolodovSvaiterVI_Alg21_halfspace
import Definitions.Def_SolodovSvaiterVI_Alg21_ArmijoHolds

namespace SolodovSvaiterVI.Alg21

/-- Lemma 2.2 of Solodov–Svaiter (p. 768), one step of Algorithm 2.1: if `k` satisfies the
linesearch condition (2.1) at `x ∈ C` with `r(x) ≠ 0`, `z = x − γᵏ r(x)` and
`H = {y | ⟨F(z), y − z⟩ ≤ 0}`, then `P_{C∩H}[x̄] = P_{C∩H}[x]` where `x̄ = P_H[x]`. -/
theorem lemma2_2_proj_xbar_eq {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCc : IsClosed C) (hCcv : Convex ℝ C)
    (hF : Continuous F) (hS : (viSol F C).Nonempty) (h12 : SatisfiesCond12 F C)
    (gamma sigma : ℝ) (hγ0 : 0 < gamma) (hγ1 : gamma < 1) (hσ0 : 0 < sigma) (hσ1 : sigma < 1)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ C) (hr : residual F C x ≠ 0)
    (k : ℕ) (hk : ArmijoHolds F C gamma sigma x k) :
    let z := x - gamma ^ k • residual F C x
    let H := halfspace (F z) z
    projOnto (C ∩ H) (projOnto H x) = projOnto (C ∩ H) x := by sorry

end SolodovSvaiterVI.Alg21
