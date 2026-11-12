-- Prove2me | Theorems.Thm_QPVEntanglement_lemma_6
-- name    : QPVEntanglement.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:23.736885+00:00
-- url     : https://prove2.me/theorems/f4667b26-8fe4-4323-8ccb-c87172deec18
-- title:
--   Lemma 6 — general additivity of mutual information
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $\rho_{OA}$ be a state where $O$ decomposes into subsystems $O_1,\dots,O_k$ (of arbitrary finite dimensions). Then
--
--   $$I(O:A)_\rho\ge\sum_{j=1}^kI(O_j:A)_\rho-\Delta_O,\qquad\Delta_O:=\sum_{j=1}^kS(O_j)_\rho-S(O)_\rho.$$
--
--   The penalty $\Delta_O$ vanishes when the state on $O$ is a product; the lemma combines one-qubit estimates of correlated reference qubits.
--
--   Differences from the source:
--   - encoding: O decomposes into k subsystems O1, …, Ok; I and S → O = (j : Fin k) → Fin (dO j); published `mutualInformation` and `vnEntropy` in bits; reason: a finite tensor product of finite-dimensional systems; entropies in bits as in §3
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 6, eq. (7), p.33; proof p.65

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Lemma 6 (General additivity of Mutual-Information)**, p.33 (proof p.65). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Lemma 6, eq. (7), p.33.

Let `ρ_{OA}` be a state with `O = O₁O₂⋯O_k`. Then
`I(O : A)_ρ ≥ Σ_{j=1}^k I(O_j : A)_ρ − Δ_O`, `Δ_O := Σ_{j=1}^k S(O_j)_ρ − S(O)_ρ`.

**Formalization Note.** `O_j` has dimension `dO j` (arbitrary), `O` is the product
`(j : Fin k) → Fin (dO j)`; `S` is the published `vnEntropy` (bits); `ρ_{O_jA}` is
`coordMarginal j ρ`. -/
theorem lemma_6 {k : ℕ} {dO : Fin k → ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix (((j : Fin k) → Fin (dO j)) × A) (((j : Fin k) → Fin (dO j)) × A) ℂ)
    (hρ : IsDensity ρ) :
    ∑ j, mutualInformation (coordMarginal j ρ) -
        (∑ j, QAlgorithms.vnEntropy (QAlgorithms.traceRight (coordMarginal j ρ)) -
          QAlgorithms.vnEntropy (QAlgorithms.traceRight ρ)) ≤
      mutualInformation ρ := by sorry

end QPVEntanglement
