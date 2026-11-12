-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_5
-- name    : QPVEntanglement.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:39.588218+00:00
-- url     : https://prove2.me/theorems/40618aab-eb80-4f32-b02d-dcafa1a873a7
-- title:
--   Lemma 5 — pure-state entanglement comparison
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   For every pure state $\omega_{OA_1A_2}$,
--
--   $$E_{sq}(OA_1:A_2)_\omega\le E_{sq}(A_1:A_2)_\omega+I(O:A_2)_\omega.$$
--
--   It compares the entanglement before and after adjoining the verifier reference to one side of the cut.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 5, eq. (6), p.33; proof p.65

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Lemma 5 (Pure-State Entanglement Comparison)**, p.33 (proof p.65). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Lemma 5, eq. (6), p.33.

For any pure state `ω_{OA₁A₂}`, `E_sq(OA₁ : A₂)_ω ≤ E_sq(A₁ : A₂)_ω + I(O : A₂)_ω`.

**Formalization Note.** `ω = |ψ⟩⟨ψ|` on `O × (A₁ × A₂)`; `E_sq(OA₁ : A₂)` is `squashed` of the
regrouped matrix on `(O × A₁) × A₂`, `E_sq(A₁ : A₂)` of the marginal tracing out `O`, and
`I(O : A₂)` the published `mutualInformation` (bits) of the marginal tracing out `A₁`. -/
theorem lemma_5 {O A1 A2 : Type*} [Fintype O] [DecidableEq O] [Fintype A1] [DecidableEq A1]
    [Fintype A2] [DecidableEq A2] (ψ : O × (A1 × A2) → ℂ) (hψ : IsUnitVec ψ) :
    squashed (assocL (pureDensity ψ)) ≤
      squashed (QAlgorithms.traceLeft (pureDensity ψ)) + mutualInformation (traceMid (pureDensity ψ)) := by sorry

end QPVEntanglement
