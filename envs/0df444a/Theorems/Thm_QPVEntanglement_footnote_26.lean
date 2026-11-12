-- Prove2me | Theorems.Thm_QPVEntanglement_footnote_26
-- name    : QPVEntanglement.footnote_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:24.610643+00:00
-- url     : https://prove2.me/theorems/24b4f125-3bd0-4535-b4d1-dfea285a0e68
-- title:
--   Footnote 26, p.43 — one crossing qubit adds at most one unit
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   For every qubit $Q$ and every state on $A_0QA_1$,
--
--   $$E_{sq}(A_0:QA_1)\le E_{sq}(A_0Q:A_1)+1.$$
--
--   It bounds the entanglement gained when a replenishment qubit crosses the claimed location (Step 4 of the proof of Theorem 7).
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), §7, proof of Theorem 7, Step 4, footnote 26, p.43 (unnumbered)

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Footnote 26 (one crossing qubit adds at most one)**, p.43. Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), §7, proof of Theorem 7, Step 4, footnote 26, p.43.

For every qubit `Q` and every state on `A₀ Q A₁`, `E_sq(A₀ : QA₁) ≤ E_sq(A₀Q : A₁) + 1`.

**Formalization Note.** `ρ` on `A₀ × (Fin 2 × A₁)`; `E_sq(A₀ : QA₁)` is `squashed ρ` and
`E_sq(A₀Q : A₁)` is `squashed` of the regrouped matrix on `(A₀ × Fin 2) × A₁`. -/
theorem footnote_26 {A0 A1 : Type*} [Fintype A0] [DecidableEq A0] [Fintype A1] [DecidableEq A1]
    (ρ : Matrix (A0 × (Fin 2 × A1)) (A0 × (Fin 2 × A1)) ℂ) (hρ : IsDensity ρ) :
    squashed ρ ≤ squashed (assocL ρ) + 1 := by sorry

end QPVEntanglement
