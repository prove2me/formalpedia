-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_3
-- name    : QPVEntanglement.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:33.860749+00:00
-- url     : https://prove2.me/theorems/916519a7-7a0c-4c7c-af9c-5ed0672ce93b
-- title:
--   Lemma 3 — Bell closeness implies entanglement
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $\tau_{OW}$ be a two-qubit state with $\mathrm{TD}[\tau_{OW},\Phi^+]\le\epsilon'$ for some $0\le\epsilon'\le1/2$. Then
--
--   $$E_{sq}(O:W)_\tau\ge1-f(\epsilon')=1-\epsilon'\log_2 3-2h(\epsilon').$$
--
--   It is the dimension-independent entanglement estimate at the final recovery endpoint.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 3, eq. (4), p.32; proof p.64

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Lemma 3 (Bell Closeness Implies Entanglement)**, p.32 (proof p.64). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Lemma 3, eq. (4), p.32.

If a two-qubit state `τ_{OW}` satisfies `TD[τ_{OW}, Φ⁺] ≤ ϵ'` with `0 ≤ ϵ' ≤ 1/2`, then
`E_sq(O : W)_τ ≥ 1 − f(ϵ') = 1 − ϵ' log₂ 3 − 2h(ϵ')`. -/
theorem lemma_3 (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hτ : IsDensity τ) (ε' : ℝ)
    (h0 : 0 ≤ ε') (h1 : ε' ≤ 1 / 2) (hTD : RandPurIso.Completion.traceDist τ phiPlus ≤ ε') :
    1 - fFun ε' ≤ squashed τ := by sorry

end QPVEntanglement
