-- Prove2me | Theorems.Thm_SensitivityPoA_SmallDemand_poa_demandNormalize
-- name    : SensitivityPoA.SmallDemand.poa_demandNormalize
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T17:39:11.029889+00:00
-- url     : https://prove2.me/theorems/07764a86-971a-49bb-812d-735891cfd828
-- title:
--   §3.5, p. 22 — demand normalizations Λ_υ preserve the game space, WE and SO flows (scaled by 1/υ), and the price of anarchy
-- statement:
--   Let $\Gamma = (\tau, d)$ be a game of the game space $\mathcal G(G, \mathcal K, \mathcal S)$ and let $\upsilon > 0$. Let $\Lambda_\upsilon(\Gamma) = (\tau \circ \upsilon, d/\upsilon)$ be its demand normalization, with $(\tau_a \circ \upsilon)(x) = \tau_a(x\upsilon)$. Then:
--
--   1. $\Lambda_\upsilon(\Gamma)$ belongs to the game space;
--   2. for every path vector $f$, $f$ is a WE flow of $\Gamma$ if and only if $f/\upsilon$ is a WE flow of $\Lambda_\upsilon(\Gamma)$;
--   3. for every path vector $f$, $f$ is an SO flow of $\Gamma$ if and only if $f/\upsilon$ is an SO flow of $\Lambda_\upsilon(\Gamma)$;
--   4. for every flow $f$ of $\Gamma$, $C(\Gamma, f) = \upsilon \cdot C(\Lambda_\upsilon(\Gamma), f/\upsilon)$;
--   5. the price of anarchy is invariant:
--   $$\rho(\Lambda_\upsilon(\Gamma)) = \rho(\Gamma).$$
--
--   Rescaling the demand to total demand $1$ in this way is what lets the small-demand regime be compared with a fixed reference game of total demand $1$.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 22, §3.5 (demand normalizations)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SensitivityPoA_SmallDemand_Setting

namespace SensitivityPoA.SmallDemand

open KellyStochasticNetworks

/-- §3.5, p. 22: a demand normalization `Λ_υ` maps the game space into itself; `˜f` and `f∗`
are a WE flow and an SO flow of `Γ` iff `˜f/υ` and `f∗/υ` are a WE flow and an SO flow of
`Λ_υ(Γ)`; `C(Γ, f) = υ · C(Λ_υ(Γ), f/υ)` for every flow `f` of `Γ`; hence `ρ(Λ_υ(Γ)) = ρ(Γ)`. -/
theorem poa_demandNormalize {N : Network} (Γ : Game N) (hΓ : Γ ∈ gameSpace N) (υ : ℝ)
    (hυ : 0 < υ) :
    demandNormalize υ Γ ∈ gameSpace N ∧
    (∀ f : Fin N.R → ℝ, IsWE Γ f ↔ IsWE (demandNormalize υ Γ) (fun r => f r / υ)) ∧
    (∀ f : Fin N.R → ℝ, IsSO Γ f ↔ IsSO (demandNormalize υ Γ) (fun r => f r / υ)) ∧
    (∀ f : Fin N.R → ℝ, IsFlow Γ f →
      cost Γ f = υ * cost (demandNormalize υ Γ) (fun r => f r / υ)) ∧
    PoA (demandNormalize υ Γ) = PoA Γ := by sorry

end SensitivityPoA.SmallDemand
