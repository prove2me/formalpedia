-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_lasserre_theorem_3_3
-- name    : RobustPMI.Hierarchy.lasserre_theorem_3_3
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-31T00:07:22.415821+00:00
-- url     : https://prove2.me/theorems/2ed25d56-aedb-4fd1-be17-6d2d62a15e51
-- title:
--   Lasserre's convex Positivstellensatz (Thm 3.3(a)): $g-g^\star=\sigma_0+\sum_j\lambda_j\theta_j$ for SOS-convex problems under Slater
-- statement:
--   Let $g,\theta_1,\dots,\theta_s\in\mathbb R[y]$, $y\in\mathbb R^\ell$, and $\mathcal Y=\{y:\theta_1(y)\ge0,\dots,\theta_s(y)\ge0\}$. Assume:
--
--   - $g$ and $-\theta_1,\dots,-\theta_s$ are **SOS-convex**, i.e. their Hessians are SOS matrices;
--   - **Slater's condition** holds: some $\bar y$ has $\theta_j(\bar y)>0$ for all $j$;
--   - the infimum of $g$ over $\mathcal Y$ is attained at some $y^\star\in\mathcal Y$.
--
--   Then there exist an SOS polynomial $\sigma_0$ and multipliers $\lambda_1,\dots,\lambda_s\ge0$ such that
--   $$g(y)-g(y^\star)=\sigma_0(y)+\sum_{j=1}^s\lambda_j\theta_j(y).$$
--
--   This is part (a) of Lasserre's Theorem 3.3, $f-f^\star\in Q_c(g)$, with $Q_c$ as in his (3.1). It says that for SOS-convex problems the optimal value is certified at the lowest level, with constant multipliers. Guo–Wang use it as [33, Theorem 3.3] in the proof of Proposition 4.6 (p. 20). There it is applied to the Lagrangian $f(y)-\mathscr L_{\Phi^\star}(P(y,x))$, which yields the certificate (4.6) $f-f^\star-\mathscr L_{\Phi^\star}(P)\in\mathcal Q_{\lceil k_y/2\rceil}(\Theta)$.
--
--   The standard proof takes KKT multipliers $\lambda$, which exist by Slater's condition. The Lagrangian $g-g(y^\star)-\sum_j\lambda_j\theta_j$ is then SOS-convex, vanishes at $y^\star$ and has zero gradient there, so it is SOS by Helton–Nie (Lemma 8).
--
--   **Formalization note.** Lasserre's $Q_c$ also asks $\sigma_0$ to be convex. This statement keeps only the SOS property, which is what the hierarchy uses.
-- source:
--   J. B. Lasserre, Convexity in semialgebraic geometry and polynomial optimization, SIAM J. Optim. 19 (2009) 1995-2014 (arXiv:0806.3784), Theorem 3.3(a) with Q_c(g) from (3.1); cited as [33, Theorem 3.3] in Guo-Wang, arXiv:2304.12628v5, proof of Proposition 4.6, p. 20

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open MvPolynomial

/-- Lasserre (2009), Theorem 3.3(a), as cited in Guo–Wang, proof of Proposition 4.6 ([33, Theorem 3.3]):
if `g` and `−θ₁, …, −θ_s` are SOS-convex, Slater's condition holds for `𝒴 = {θ ≥ 0}`, and `g` attains
its infimum over `𝒴` at `y⋆`, then `g − g(y⋆) = σ₀ + ∑ⱼ λⱼ θⱼ` with `σ₀` SOS and `λ ≥ 0`. -/
theorem lasserre_theorem_3_3 {ℓ s : ℕ} (g : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ) (hg : IsSOSConvex g) (hθ : ∀ j, IsSOSConvex (-θ j))
    (hslater : ∃ y : Fin ℓ → ℝ, ∀ j, 0 < eval y (θ j))
    (ys : Fin ℓ → ℝ) (hys : ys ∈ Yset θ) (hmin : ∀ y ∈ Yset θ, eval ys g ≤ eval y g) :
    ∃ (σ₀ : MvPolynomial (Fin ℓ) ℝ) (lam : Fin s → ℝ), IsSOSPoly σ₀ ∧ (∀ j, 0 ≤ lam j) ∧
      g - C (eval ys g) = σ₀ + ∑ j, C (lam j) * θ j := by sorry

end RobustPMI.Hierarchy
