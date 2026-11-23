-- Prove2me | Theorems.Thm_PlatonicJEPA_nuisance_costs_alignment
-- name    : PlatonicJEPA.nuisance_costs_alignment
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:25:14.07747+00:00
-- url     : https://prove2.me/theorems/b7d64c19-5fe4-4795-ad8d-9e4f698832a2
-- title:
--   Theorem 3: nuisance costs alignment
-- statement:
--   Let $f_1$ and $f_2$ be centred, whitened encoders of two modalities into $\mathbb{R}^k$, $k\ge1$, written $e_m(z,\nu)$ on observations of state $z$ with nuisance $\nu\sim q_m$, the state and the nuisances being independent. Over paired observations $(x_1,x_2)$ of one world state with independent nuisances, for every $Q\in O(k)$,
--
--   $$E\,\|Qf_1(x_1)-f_2(x_2)\|^2\ge2k\Big(1-\min_m\rho(f_m)\Big),$$
--
--   and $\rho(f_m)=1$ if and only if $f_m(x)$ is a function of the world state alone.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2.3, Theorem 3, eq. (4), p. 5; proof in Appendix A.4

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem nuisance_costs_alignment {Z N₁ N₂ : Type*} [Fintype Z] [DecidableEq Z] [Fintype N₁]
    [Fintype N₂] {k : ℕ} (hk : 1 ≤ k)
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (q₁ : N₁ → ℝ) (hq₁ : ∀ ν, 0 < q₁ ν) (hq₁1 : ∑ ν, q₁ ν = 1)
    (q₂ : N₂ → ℝ) (hq₂ : ∀ ν, 0 < q₂ ν) (hq₂1 : ∑ ν, q₂ ν = 1)
    (e₁ : Z → N₁ → Fin k → ℝ) (e₂ : Z → N₂ → Fin k → ℝ)
    (he₁ : IsWhitenedObs p q₁ e₁) (he₂ : IsWhitenedObs p q₂ e₂) :
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      2 * k * (1 - min (rho p q₁ e₁) (rho p q₂ e₂)) ≤
        ∑ z, ∑ ν₁, ∑ ν₂, p z * q₁ ν₁ * q₂ ν₂ * sqNorm (rot Q (e₁ z ν₁) - e₂ z ν₂)) ∧
    (rho p q₁ e₁ = 1 ↔ ∀ z ν ν', e₁ z ν = e₁ z ν') ∧
    (rho p q₂ e₂ = 1 ↔ ∀ z ν ν', e₂ z ν = e₂ z ν') := by sorry

end PlatonicJEPA
