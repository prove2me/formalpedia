-- Prove2me | Theorems.Thm_QPVEntanglement_corollary_2
-- name    : QPVEntanglement.corollary_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:32:54.683002+00:00
-- url     : https://prove2.me/theorems/a846d6c7-2873-4310-b5ba-c334e3d7bb0b
-- title:
--   Corollary 2 — classical records on both sides
-- statement:
--   This mission states the paper's results in the **operator-requested pinned-down model** of its §4 adversary model; this item is a pure quantum-information statement and does not depend on that model.
--
--   Let $A_0=C_0A_0'$ and $A_1=C_1A_1'$. For each value $c=(c_0,c_1)$ of the two records (probability $p_c$) let $(r_1(c),\dots,r_k(c))$ be $k$ distinct reference-qubit labels and $O_j:=O_{r_j(c)}$. Suppose $\rho_{OA_0A_1}=\sum_cp_c|c_0\rangle\langle c_0|_{C_0}\otimes|c_1\rangle\langle c_1|_{C_1}\otimes|\psi_c\rangle\langle\psi_c|_{OA_0'A_1'}$ with every $|\psi_c\rangle$ pure, $\Lambda$ is an LOCC channel across $A_0:A_1$ that leaves $C_0,C_1$ and the reference qubits unchanged, $\tau=(\mathcal I_O\otimes\Lambda)(\rho)$, and for every $c,j$ there are recovery maps $\mathcal E^c_j$ on $A_0'$ and $\mathcal F^c_j$ on $A_1'$ (depending on the complete $c$) with
--
--   $$\frac1k\sum_cp_c\sum_{j=1}^kF(\tilde\rho^{c,j}_{O_jR_j},\Phi^+)\ge1-\epsilon^2,\ 0\le\epsilon\le\tfrac34,\qquad\frac1k\sum_cp_c\sum_{j=1}^kF(\tilde\tau^{c,j}_{O_jW_j},\Phi^+)\ge1-(\epsilon')^2,\ 0\le\epsilon'\le\tfrac12.$$
--
--   Then
--
--   $$E_{sq}(A_0:A_1)_\rho-E_{sq}(A_0:A_1)_\tau\ge k\big[1-2g(\epsilon)-f(\epsilon')\big].$$
--
--   It is the form of the consumption bound applied in Step 3 of the proof of Theorem 7.
--
--   Differences from the source:
--   - encoding: E_sq = ½ inf over all extensions ω_ABE of I(A:B|E) → published `squashed`: ½·sInf of the conditional mutual information (bits) over density-matrix extensions with environment `Fin e`, every e > 0; reason: every finite-dimensional extension is isomorphic to one with E = Fin e; same quantity
--   - encoding: an LOCC channel Λ across A1 : A2 → `IsLOCCAcross Λ`: after relabelling basis indices, a published `FiniteLOCC` protocol (finite adaptive rounds, complete local Kraus instruments); output registers arbitrary; reason: standard finite-round LOCC, the class of fact (ii), p.26
--   - encoding: (1/k) Σ_{j=1}^k …, k qubits → hypothesis 0 < k; reason: excludes only the undefined average at k = 0
--   - reading: Λ leaves C0, C1 unchanged → every input with a definite record value c is mapped to an output with the same definite record value (`flagSector`); Λ's quantum outputs B0, B1 arbitrary; reason: the inputs are classical in C0, C1, so only the record sectors matter; the weakest form of 'unchanged' gives the strongest statement
--   - encoding: reference qubits O_{r_j(c)}; the reference qubits unchanged → a pool Fin N → Fin 2 of labelled qubits, r c : Fin k ↪ Fin N; O is not an input of Λ (I_O ⊗ Λ); reason: k distinct labels from a finite pool; Λ acts on A0A1 only
--   - encoding: recovery maps E^c_j on A′0, F^c_j on A′1; Σ_c p_c F(τ̃^{c,j}, Φ⁺) → CPTP E^c_j : A′0 → ℂ² ⊗ P_j, F^c_j : B1 → ℂ² ⊗ Q_j; Σ_c F of the pair marginal of the unnormalized record-c block of τ; reason: p_c · F(normalized conditional state) is F of the unnormalized block, F being linear (overlap with pure Φ⁺)
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Corollary 2, eqs. (17)–(22), p.35; proof p.72

import Mathlib
import Definitions.Def_QPVEntanglement_flaggedState
import Definitions.Def_QPVEntanglement_pairMarginal
import Definitions.Def_QPVEntanglement_gSafe
import Definitions.Def_QPVEntanglement_IsLOCCAcross

set_option autoImplicit false

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P19 (squashed mutualInformation)

namespace QPVEntanglement

/-- **Corollary 2 (Classical Records on Both Sides)**, p.35 (proof p.72). Behera–Goyal,
arXiv:2609.39234 (sha256 bdf2928d…), Corollary 2, eqs. (17)–(22), p.35.

Let `A₀ = C₀A₀'`, `A₁ = C₁A₁'`, and for each record value `c = (c₀, c₁)` (probability `p_c`)
let `(r₁(c), …, r_k(c))` be `k` distinct reference-qubit labels, `O_j := O_{r_j(c)}`. Let
`ρ = Σ_c p_c |c₀⟩⟨c₀| ⊗ |c₁⟩⟨c₁| ⊗ |ψ_c⟩⟨ψ_c|_{OA₀'A₁'}` with every `ψ_c` pure, `Λ` an LOCC
channel across `A₀ : A₁` that leaves `C₀, C₁` and the reference qubits unchanged,
`τ = (I_O ⊗ Λ)(ρ)`, and `E^c_j` on `A₀'`, `F^c_j` on `A₁'` recovery maps (depending on the
complete `c`) with
`(1/k) Σ_c p_c Σ_j F(ρ̃^{c,j}_{O_jR_j}, Φ⁺) ≥ 1 − ϵ²`, `0 ≤ ϵ ≤ 3/4`, and
`(1/k) Σ_c p_c Σ_j F(τ̃^{c,j}_{O_jW_j}, Φ⁺) ≥ 1 − (ϵ')²`, `0 ≤ ϵ' ≤ 1/2`. Then
`E_sq(A₀ : A₁)_ρ − E_sq(A₀ : A₁)_τ ≥ k[1 − 2g(ϵ) − f(ϵ')]`.

**Formalization Note.** The reference register is a pool of `N` labelled qubits
`Fin N → Fin 2`; `r c : Fin k ↪ Fin N`. "Leaves `C₀, C₁` unchanged": `Λ` maps every input with
definite record `c` to an output with the same definite record (`flagSector`); its quantum
outputs `B₀, B₁` are arbitrary; "leaves the reference qubits unchanged": `O` is not an input of
`Λ` (`I_O ⊗ Λ`). The maps `E^c_j : A₀' → ℂ² ⊗ P_j` and `F^c_j : B₁ → ℂ² ⊗ Q_j` are CPTP, `R_j,
W_j` their `ℂ²` output factors. In (21) `p_c·τ̃^{c,j}` is the marginal of the unnormalized
record-`c` block `⟨c|τ|c⟩` (equal to `p_c` times the conditional state). `0 < k` excludes
only the undefined average. -/
theorem corollary_2 {k Nref : ℕ} {C0 C1 A0 A1 B0 B1 : Type*} [Fintype C0] [DecidableEq C0]
    [Fintype C1] [DecidableEq C1] [Fintype A0] [DecidableEq A0] [Fintype A1] [DecidableEq A1]
    [Fintype B0] [DecidableEq B0] [Fintype B1] [DecidableEq B1]
    {P Q : Fin k → Type*} [∀ j, Fintype (P j)] [∀ j, Fintype (Q j)] (hk : 0 < k)
    (r : C0 × C1 → (Fin k ↪ Fin Nref)) (p : C0 × C1 → ℝ)
    (ψ : C0 × C1 → (Fin Nref → Fin 2) × (A0 × A1) → ℂ) (hp : IsProbVec p)
    (hψ : ∀ c, IsUnitVec (ψ c))
    (Λ : QAlgorithms.Superop ((C0 × A0) × (C1 × A1)) ((C0 × B0) × (C1 × B1)))
    (hΛ : IsLOCCAcross Λ)
    (hflag : ∀ (c : C0 × C1) (X : Matrix (A0 × A1) (A0 × A1) ℂ),
      ∃ Y : Matrix (B0 × B1) (B0 × B1) ℂ, Λ (flagSector c X) = flagSector c Y)
    (E : C0 × C1 → (j : Fin k) → QAlgorithms.Superop A0 (Fin 2 × P j))
    (hE : ∀ c j, QAlgorithms.IsChannel (E c j))
    (F : C0 × C1 → (j : Fin k) → QAlgorithms.Superop B1 (Fin 2 × Q j))
    (hF : ∀ c j, QAlgorithms.IsChannel (F c j))
    (ε ε' : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 3 / 4) (hε' : 0 ≤ ε' ∧ ε' ≤ 1 / 2)
    (hinit : 1 - ε ^ 2 ≤ (1 / (k : ℝ)) * ∑ c, p c * ∑ j, bellOverlap
      (pairMarginal (qubitAt (r c j)) (Equiv.prodAssoc (Fin 2) (P j) A1)
        (applyMid (E c j) (pureDensity (ψ c)))))
    (hfin : 1 - ε' ^ 2 ≤ (1 / (k : ℝ)) * ∑ c, ∑ j, bellOverlap
      (pairMarginal (qubitAt (r c j)) (extRight (A := B0) (Equiv.refl (Fin 2 × Q j)))
        (QAlgorithms.idTensorSuperop (QAlgorithms.idTensorSuperop (F c j))
          (sectorBlock c (QAlgorithms.idTensorSuperop Λ (flaggedState2 p ψ)))))) :
    (k : ℝ) * (1 - 2 * gFun ε - fFun ε') ≤
      squashed (QAlgorithms.traceLeft (flaggedState2 p ψ)) -
        squashed (QAlgorithms.traceLeft (QAlgorithms.idTensorSuperop Λ (flaggedState2 p ψ))) := by sorry

end QPVEntanglement
