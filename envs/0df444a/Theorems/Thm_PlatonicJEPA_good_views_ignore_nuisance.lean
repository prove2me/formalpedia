-- Prove2me | Theorems.Thm_PlatonicJEPA_good_views_ignore_nuisance
-- name    : PlatonicJEPA.good_views_ignore_nuisance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:27:21.17194+00:00
-- url     : https://prove2.me/theorems/d5d5b52e-dc60-4fd6-8134-286314556f3d
-- title:
--   Proposition 3 (i): good views ignore nuisance
-- statement:
--   Take the objective of Proposition 1 on observations $(z,\nu)$, with nuisance $\nu\sim q$ independent of $z$, and a good-view JEPA whose positive pairs have law $\pi(z,z')q(\nu)q(\nu')$. Let $1\le k<|Z|$ and $\mu_k>\max(\mu_{k+1},0)$. Then the minimisers of the good-view objective are exactly the embeddings $e(z,\nu)=a(z)$ with $a$ a spectral minimiser of $\pi$. These are the embeddings $Q\Phi_\pi(z)$, which are functions of the state alone. Good-view JEPAs of two modalities with the same world kernel $\pi$ agree up to one rotation on every observation: $e_1(z,\nu_1)=Qe_2(z,\nu_2)$ for all $z,\nu_1,\nu_2$.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Section 2.3, Proposition 3 (i), p. 5; formal statement in Appendix A.4, p. 21

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem good_views_ignore_nuisance {Z N₁ N₂ : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype N₁] [DecidableEq N₁] [Fintype N₂] [DecidableEq N₂] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π) (hk : 1 ≤ k) (hkZ : k < Fintype.card Z)
    (q₁ : N₁ → ℝ) (hq₁ : ∀ ν, 0 < q₁ ν) (hq₁1 : ∑ ν, q₁ ν = 1)
    (q₂ : N₂ → ℝ) (hq₂ : ∀ ν, 0 < q₂ ν) (hq₂1 : ∑ ν, q₂ ν = 1)
    (hpos : 0 < eigs p π k) (hgap : k + 1 < Fintype.card Z → eigs p π (k + 1) < eigs p π k) :
    (∀ e : Z × N₁ → Fin k → ℝ,
      IsSpectralMin (fun x => p x.1 * q₁ x.2) (goodViewLaw π q₁) e ↔
        ∃ a : Z → Fin k → ℝ, IsSpectralMin p π a ∧ ∀ x, e x = a x.1) ∧
    (∀ (e₁ : Z × N₁ → Fin k → ℝ) (e₂ : Z × N₂ → Fin k → ℝ),
      IsSpectralMin (fun x => p x.1 * q₁ x.2) (goodViewLaw π q₁) e₁ →
      IsSpectralMin (fun x => p x.1 * q₂ x.2) (goodViewLaw π q₂) e₂ →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z ν₁ ν₂, e₁ (z, ν₁) = rot Q (e₂ (z, ν₂))) := by sorry

end PlatonicJEPA
