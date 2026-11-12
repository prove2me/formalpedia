-- Prove2me | Theorems.Thm_QPVEntanglement_corollary_1
-- name    : QPVEntanglement.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:48.193658+00:00
-- url     : https://prove2.me/theorems/52848c2a-75fd-4c9c-b352-1aaf1cbcbc30
-- title:
--   Corollary 1 — local recovery by quantum channels
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $O$, $\rho_{OA_1A_2}$ be as in Theorem 6. Suppose there are $k$ local quantum channels (CPTP maps) $\mathcal E_j$ on $A_1$ that do not scramble the classical flag register, with $\frac1k\sum_jF(\tilde\rho^{(j)}_{O_jR_j},\Phi^+)\ge1-\epsilon^2$, $0\le\epsilon\le3/4$; an LOCC channel $\Lambda$ across $A_1:A_2$ gives $\tau=(\mathcal I_O\otimes\Lambda)(\rho)$; and $k$ local channels $\mathcal F_j$ on $A_2$ satisfy $\frac1k\sum_jF(\tilde\tau^{(j)}_{O_jW_j},\Phi^+)\ge1-(\epsilon')^2$, $0\le\epsilon'\le1/2$. Then
--
--   $$\Delta E_{sq}\ge k\big[1-2g(\epsilon)-f(\epsilon')\big].$$
--
--   It extends Theorem 6 to arbitrary recovery channels.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - encoding: an LOCC channel Λ across A1 : A2 → `IsLOCCAcross Λ`: after relabelling basis indices, a published `FiniteLOCC` protocol (finite adaptive rounds, complete local Kraus instruments); output registers arbitrary; reason: standard finite-round LOCC, the class of fact (ii), p.26
--   - encoding: (1/k) Σ_{j=1}^k …, k qubits → hypothesis 0 < k; reason: excludes only the undefined average at k = 0
--   - reading: local quantum channels on A1 that do not scramble the classical flag register → E_j = Σ_c |c⟩⟨c| ⊗ E^c_j with CPTP E^c_j : A′1 → ℂ² ⊗ P_j (classically controlled, flag unchanged); recovered marginal Σ_c p_c·(O_jR_j-marginal of (id ⊗ E^c_j ⊗ id)|ψ_c⟩⟨ψ_c|); reason: the proof (p.71) uses exactly maps 'classically controlled by the flag registers' that 'leave the original flag registers unchanged'
--   - encoding: target R_j, W_j; F(·, Φ⁺) → the ℂ² output factor of E^c_j : A′1 → ℂ² ⊗ P_j and of F_j : B2 → ℂ² ⊗ Q_j; overlap with Φ⁺; reason: a channel's output with a selected qubit is ℂ² ⊗ (rest); F against pure Φ⁺ is the overlap
--   - reading: ΔE_sq → E_sq(A1:A2)_ρ − E_sq(A1:A2)_τ; reason: as written in (94), p.72
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Corollary 1, eqs. (14)–(16), pp.34–35; proof p.71

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe
import Definitions.Def_QPVEntanglement_IsLOCCAcross

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Corollary 1 (Local Recovery by Quantum Channels)**, pp.34–35 (proof p.71). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Corollary 1, eqs. (14)–(16), pp.34–35.

As Theorem 6, with the recovery unitaries replaced by local quantum channels (CPTP maps):
`E_j` on `A₁` that do not scramble the classical flag register, with
`(1/k) Σ_j F(ρ̃^{(j)}_{O_jR_j}, Φ⁺) ≥ 1 − ϵ²`, `0 ≤ ϵ ≤ 3/4`; an LOCC channel `Λ` across
`A₁ : A₂`, `τ = (I_O ⊗ Λ)(ρ)`; channels `F_j` on `A₂` with
`(1/k) Σ_j F(τ̃^{(j)}_{O_jW_j}, Φ⁺) ≥ 1 − (ϵ')²`, `0 ≤ ϵ' ≤ 1/2`. Then
`ΔE_sq ≥ k[1 − 2g(ϵ) − f(ϵ')]`.

**Formalization Note.** "Does not scramble the classical flag register" is read as classically
controlled by the flag and leaving it unchanged (proof, p.71): `E_j = Σ_c |c⟩⟨c| ⊗ E^c_j` with
CPTP `E^c_j : A₁' → ℂ² ⊗ P_j`, `R_j` the `ℂ²` output factor; on the classically flagged `ρ`
the recovered marginal is `ρ̃^{(j)} = Σ_c p_c (O_jR_j-marginal of (id ⊗ E^c_j ⊗ id)|ψ_c⟩⟨ψ_c|)`.
`F_j : B₂ → ℂ² ⊗ Q_j` (CPTP), `W_j` its `ℂ²` output factor. `0 < k` excludes only the
undefined average. -/
theorem corollary_1 {k : ℕ} {C A1 A2 B1 B2 : Type*} [Fintype C] [DecidableEq C] [Fintype A1]
    [DecidableEq A1] [Fintype A2] [DecidableEq A2] [Fintype B1] [DecidableEq B1] [Fintype B2]
    [DecidableEq B2] {P Q : Fin k → Type*} [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)]
    (hk : 0 < k) (p : C → ℝ) (ψ : C → (Fin k → Fin 2) × (A1 × A2) → ℂ) (hp : IsProbVec p)
    (hψ : ∀ c, IsUnitVec (ψ c))
    (E : (j : Fin k) → C → QAlgorithms.Superop A1 (Fin 2 × P j))
    (hE : ∀ j c, QAlgorithms.IsChannel (E j c)) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 3 / 4)
    (hinit : 1 - ε ^ 2 ≤ (1 / (k : ℝ)) * ∑ j, bellOverlap (∑ c, (p c : ℂ) •
      pairMarginal (qubitAt j) (Equiv.prodAssoc (Fin 2) (P j) A2)
        (applyMid (E j c) (pureDensity (ψ c)))))
    (Λ : QAlgorithms.Superop ((C × A1) × A2) (B1 × B2)) (hΛ : IsLOCCAcross Λ)
    (F : (j : Fin k) → QAlgorithms.Superop B2 (Fin 2 × Q j))
    (hF : ∀ j, QAlgorithms.IsChannel (F j)) (ε' : ℝ) (hε' : 0 ≤ ε' ∧ ε' ≤ 1 / 2)
    (hfin : 1 - ε' ^ 2 ≤ (1 / (k : ℝ)) * ∑ j, bellOverlap (pairMarginal (qubitAt j)
      (extRight (A := B1) (Equiv.refl (Fin 2 × Q j)))
      (QAlgorithms.idTensorSuperop (QAlgorithms.idTensorSuperop (F j))
        (QAlgorithms.idTensorSuperop Λ (flaggedState p ψ))))) :
    (k : ℝ) * (1 - 2 * gFun ε - fFun ε') ≤
      squashed (QAlgorithms.traceLeft (flaggedState p ψ)) -
        squashed (QAlgorithms.traceLeft (QAlgorithms.idTensorSuperop Λ (flaggedState p ψ))) := by sorry

end QPVEntanglement
