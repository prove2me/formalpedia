-- Prove2me | Theorems.Thm_PassiveAdiabaticFT_Thermal_lemma_3_1
-- name    : PassiveAdiabaticFT.Thermal.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:45.107059+00:00
-- url     : https://prove2.me/theorems/144a10d9-47cf-4f4c-9e51-3af3ecc8569c
-- title:
--   Lemma 3.1 — dissipator and Lamb shift versus the classical syndrome chain
-- statement:
--   Let $H=\sum_iH_0^{(i)}+\hat K$ be the physical Hamiltonian (3.1) at a fixed time, with $K$ a Hermitian logical Hamiltonian, and let the rates satisfy (1.18)–(1.19). Let $p$ be any probability distribution on $\Omega^N$ and $\sigma_{Q,R}$ any joint logical–reference state. For every block $i$ and single-qubit Pauli $F_\alpha$:
--
--   1. for the dissipative part,
--   $$\Big\|\Big(\sum_\omega\gamma_\alpha^{(\omega)}D[F^{(i)}_{\alpha,\omega}]\otimes\mathcal I_R\Big)(\bar\sigma_p)-\bar\sigma_{\mathsf M_\alpha^{(i)}p}\Big\|_1\le2\gamma\,p(D_\alpha^{(i)});\qquad(3.8)$$
--   2. for the Lamb shift, with $H^{(i)}_{LS,\alpha}=\sum_\omega\kappa_\alpha^{(\omega)}F^{(i)\dagger}_{\alpha,\omega}F^{(i)}_{\alpha,\omega}$,
--   $$\big\|[H^{(i)}_{LS,\alpha}\otimes I_R,\bar\sigma_p]\big\|_1\le2\kappa\,p(D_\alpha^{(i)}).\qquad(3.9)$$
--
--   Outside the dangerous syndromes the thermal noise acts only as the classical chain $\mathsf M_\alpha^{(i)}$ on the syndrome register, leaving the logical state untouched; the error is controlled by the weight of the dangerous sector.
--
--   Differences from the source:
--   - encoding: ‖·‖₁ → QAlgorithms.traceNorm M = Re Tr √(M†M); reason: the trace norm, unhalved as printed
--   - encoding: the Hamiltonian H(t) at time t → a fixed Hermitian logical Hamiltonian K (the value K(t)) and H = Σ_i H_0^{(i)} + K̂; reason: the lemma is pointwise in t
--   - generalization: the penalty J > 0 of the construction → any real J; reason: the proof does not use the sign of J; J > 0 is an instance
-- source:
--   Arsalan Motamedi, Peter Love, Fault Tolerant Adiabatic Quantum Computation from Passive Error Correcting Codes, STOC 2027 submission #1144 (October 2026), source.pdf SHA-256 96d4a748a9114e6a9ed0c5252e84434a63b2a1ef07b286134f01f6761c2503b8, p. 21, Lemma 3.1 (3.8)–(3.9) (proof pp. 21–23)

import Mathlib
import Definitions.Def_PassiveAdiabaticFT_Thermal_Blocks

set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix ComplexOrder

namespace PassiveAdiabaticFT.Thermal

/-- Lemma 3.1 (p. 21): for any probability vector `p` on `Ω^N` and any joint logical–reference
state `σ`, with `H = Σ_i H_0^{(i)} + K̂` for a Hermitian logical `K`:
(1) `‖(Σ_ω γ_α^{(ω)} D[F_{α,ω}^{(i)}] ⊗ I_R)(σ̄_p) − σ̄_{M_α^{(i)} p}‖₁ ≤ 2γ p(D_α^{(i)})` (3.8);
(2) `‖[H_{LS,α}^{(i)} ⊗ I_R, σ̄_p]‖₁ ≤ 2κ p(D_α^{(i)})` (3.9). -/
theorem lemma_3_1 {b : ℕ} (C : StabCode b) (D : PauliDecoder C) (N : ℕ) (J β γ κ : ℝ)
    (γr κr : Fin N × (Fin b × Fin 3) → ℝ → ℝ) (hrates : RatesAdmissible β γ κ γr κr)
    (K : Op (Fin N × Fin C.k)) (hK : K.IsHermitian) {R : Type} [Fintype R] [DecidableEq R]
    (σ : Matrix ((Fin N × Fin C.k → Fin 2) × R) ((Fin N × Fin C.k → Fin 2) × R) ℂ)
    (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (p : (Fin N → C.Om) → ℝ) (hp0 : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (i : Fin N) (α : Fin b × Fin 3) :
    QAlgorithms.traceNorm
        ((∑ ω ∈ bohrFreqs (D.Hphys N J K), ((γr (i, α) ω : ℝ) : ℂ) •
            dissipator (liftRef (R := R) (bohrComp (D.Hphys N J K) (PauliDecoder.Fphys N (i, α)) ω))
              (D.sigmaBar N σ p)) -
          D.sigmaBar N σ (D.MN N J i α (γr (i, α)) p)) ≤
        2 * γ * C.massN N p (D.DsetN N i α) ∧
    QAlgorithms.traceNorm
        (liftRef (R := R) (∑ ω ∈ bohrFreqs (D.Hphys N J K), ((κr (i, α) ω : ℝ) : ℂ) •
              ((bohrComp (D.Hphys N J K) (PauliDecoder.Fphys N (i, α)) ω)ᴴ *
                bohrComp (D.Hphys N J K) (PauliDecoder.Fphys N (i, α)) ω)) * D.sigmaBar N σ p -
          D.sigmaBar N σ p * liftRef (R := R) (∑ ω ∈ bohrFreqs (D.Hphys N J K),
            ((κr (i, α) ω : ℝ) : ℂ) •
              ((bohrComp (D.Hphys N J K) (PauliDecoder.Fphys N (i, α)) ω)ᴴ *
                bohrComp (D.Hphys N J K) (PauliDecoder.Fphys N (i, α)) ω))) ≤
        2 * κ * C.massN N p (D.DsetN N i α) := by sorry

end PassiveAdiabaticFT.Thermal
