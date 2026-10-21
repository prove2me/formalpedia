-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_proposition_3_2
-- name    : SystemicDiv.SellOff.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:29.91403+00:00
-- url     : https://prove2.me/theorems/550da24f-f170-4b74-88c7-580ea027e8db
-- title:
--   Proposition 3.2, p. 14 — the fire-sale game is a potential game, and has a pure-strategy Nash equilibrium
-- statement:
--   Consider $N$ banks and $K \ge 1$ assets with illiquidity parameters $\gamma_k > 0$, banks satisfying the standing assumptions, and a shock law $\mu$ with $E\|Z\|^2 < \infty$.
--
--   1. The game is a **potential game** with potential $P$ of (3.2): for every bank $i$, every profile $\pi_{-i}$ of the others in $\Pi^{N-1}$, and all $\pi^{(1)}_i, \pi^{(2)}_i \in \Pi$,
--   $$\mathrm{EC}_i(\pi^{(1)}_i,\pi_{-i}) - \mathrm{EC}_i(\pi^{(2)}_i,\pi_{-i}) = P(\pi^{(1)}_i,\pi_{-i}) - P(\pi^{(2)}_i,\pi_{-i}).$$
--   2. If moreover $Z$ is a continuous random vector (its law is absolutely continuous with respect to Lebesgue measure on $\mathbb R^K$), the game admits a pure-strategy Nash equilibrium.
--
--   The potential reduces the search for an equilibrium to the minimization of a single function, and is the tool behind every equilibrium result of the paper.
--
--   **Formalization Note.** Part 1 uses the published definition `MondererShapley.ClosedPath.IsPotential` on the strategy sets $\Pi$ (as a subtype); its identity is exactly (3.1). The finite second moment is added, so that the integrals split. $K \ge 1$ is added: for $K = 0$ the action set is empty and part 2 would fail.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 14, Proposition 3.2, eqs. (3.1), (3.2)

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotential
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Proposition 3.2, p. 14: the fire-sale game is a potential game with potential (3.2), i.e. (3.1)
holds on `Π^N`; and if `Z` is a continuous random vector (its law is absolutely continuous w.r.t.
Lebesgue measure on `ℝ^K`), the game has a pure-strategy Nash equilibrium. -/
theorem proposition_3_2 {N K : ℕ} (hK : 0 < K) (μ : Measure (Shock K)) [IsProbabilityMeasure μ]
    (hM2 : SecondMoment μ) (B : Fin N → Bank) (hB : ∀ i, (B i).Standing)
    (γ : Fin K → ℝ) (hγ : ∀ k, 0 < γ k) :
    MondererShapley.ClosedPath.IsPotential
        (Y := fun _ : Fin N => ↥(stdSimplex ℝ (Fin K)))
        (fun i y => EC μ B γ (fun j => (y j : Fin K → ℝ)) i)
        (fun y => Pot μ B γ (fun j => (y j : Fin K → ℝ))) ∧
      (μ ≪ volume → ∃ π : Fin N → Fin K → ℝ, IsNash μ B γ π) := by sorry

end SystemicDiv.SellOff
