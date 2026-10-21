-- Prove2me | Theorems.Thm_RenegingLD_MM1_eq_6_1_C_cont
-- name    : RenegingLD.MM1.eq_6_1_C_cont
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:24.063036+00:00
-- url     : https://prove2.me/theorems/db552ecf-cdfb-4597-a327-5bc69e6b1508
-- title:
--   §6, p. 31, (6.1) — z_γ is the unique positive root of λz⁻¹ − µz − γ = 0; C is continuous and C(λ − µ) = 0
-- statement:
--   Let $\lambda\ge\mu>0$, and let $z_\gamma=(\sqrt{\gamma^2+4\lambda\mu}-\gamma)/(2\mu)$ and $C(\gamma)=\lambda(1-z_\gamma^{-1})+\mu(1-z_\gamma)-\gamma\log z_\gamma$.
--
--   1. For $\gamma\ge0$, $z_\gamma$ is the unique positive solution $z$ of
--   $$\lambda z^{-1}-\mu z-\gamma=0. \tag{6.1}$$
--   2. The map $\gamma\mapsto C(\gamma)$ is continuous on $[0,\infty)$.
--   3. $C(\lambda-\mu)=0$.
--
--   (6.1) is used to rewrite $C(\gamma)=\lambda\ell(z_\gamma^{-1})+\mu\ell(z_\gamma)$ and in the matching lower bound; $C(\lambda-\mu)=0$ says that reneging at the fluid rate $\lambda-\mu$ costs nothing in the long run.
--
--   **Formalization Note.** "Continuous" is stated on $[0,\infty)$, the domain on which $C$ is used.
-- source:
--   Atar, Budhiraja, Dupuis & Wu, Large Deviations for the Single Server Queue and the Reneging Paradox, arXiv:1903.06870v2, p. 31, (6.1) and the sentence after it

import Mathlib
import Definitions.Def_RenegingLD_MM1_Variational

namespace RenegingLD.MM1

open MeasureTheory Filter Topology
open scoped ENNReal

theorem eq_6_1_C_cont (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hlm : mu ≤ lam) :
    (∀ γ : ℝ, 0 ≤ γ →
      0 < z lam mu γ ∧ lam * (z lam mu γ)⁻¹ - mu * z lam mu γ - γ = 0 ∧
        ∀ w : ℝ, 0 < w → lam * w⁻¹ - mu * w - γ = 0 → w = z lam mu γ) ∧
    ContinuousOn (C lam mu) (Set.Ici 0) ∧
    C lam mu (lam - mu) = 0 := by sorry

end RenegingLD.MM1
