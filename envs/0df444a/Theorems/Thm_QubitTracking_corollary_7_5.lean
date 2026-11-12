-- Prove2me | Theorems.Thm_QubitTracking_corollary_7_5
-- name    : QubitTracking.corollary_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:38.996211+00:00
-- url     : https://prove2.me/theorems/9ec92669-d0c5-4fdb-a0de-49233c17d008
-- title:
--   Corollary 7.5 — an efficient black-box extractor recovers the anchor's Hadamard-basis value in the dual game
-- statement:
--   Let $n(\lambda)\ge\lambda$ and $m_0=m_1=m(\lambda)\ge\lambda$ be polynomials, and $n_e=n$. There is an efficient extractor $\mathcal E_H$ with access to $\mathsf{sk}$ and the register $\mathbf M$ such that for any efficient adversary $\mathcal A$ in the dual game of Definition 7.4 (stage-0 oracle on $S^\perp+u$, stage-1 on $T+v$) with $\Pr[\ne\bot]=\varepsilon'$ an inverse polynomial and $\Pr[=1]/\Pr[\ne\bot]=1-\varepsilon$,
--   $$\mathbb E\big[\mathrm{Tr}(\Pi_{\mathrm{eq}}\,\mathcal E_H^{\mathcal A^1_M}\rho\,(\mathcal E_H^{\mathcal A^1_M})^\dagger\,\Pi_{\mathrm{eq}})\,\big|\,\text{no abort}\big]\ge1-2\sqrt2\,\varepsilon^{1/2}-\mathrm{negl}(\lambda),\qquad\Pi_{\mathrm{eq}}=\sum_xH^{\otimes n}|x\rangle\langle x|_{\mathbf A}H^{\otimes n}\otimes|x\rangle\langle x|_{\mathbf X}.$$
--   The extractor only makes black-box access to $\mathcal A^1_M$ and acts on $\mathbf M$.
--
--   It is the Hadamard-basis counterpart of Lemma 7.1.
--
--   Differences from the source:
--   - reading: an efficient adversary of the multi-stage game, with registers passed between parties (Definitions 6.1, 7.4, 7.8) → MSAdv: seven polynomial-size circuits on a finite set of qubit wires, register hand-offs as disjoint wire sets, the abort decision and the answers read from wires at the end; reason: the paper leaves the computational model of the parties informal; a party's ancillas are untouched wires and measurements are deferred, which changes no probability
--   - encoding: b₀ sampled uniformly, or purified in a register 𝐁 initialized to |+⟩ (Definition 6.1, step 3) → b₀ averaged uniformly; reason: b₀ only controls the oracle, so purification gives the same probabilities
--   - encoding: ε′(λ) any inverse polynomial → 1 ≤ p(λ)·ε′(λ) for a polynomially bounded p; reason: the same condition, written without division by p(λ) = 0
--   - reading: an efficient extractor with access to sk and the register 𝐌 that only makes black-box access to 𝒜¹_M and acts on 𝐌 → BBExt: an adversary-independent family of polynomially many ancilla gates and calls of 𝒜¹_M's unitary up to BeforeSplit (forward or inverted, possibly controlled), its oracle queries answered by circuits of the extractor, sk written on its ancillas; reason: the paper's extractors (compressed-oracle simulation in Lemma 7.1, controlled ℰ_S, ℰ_H and their reverses through Corollary 7.7 in Theorem 7.9) are of this form
--   - reading: negl(λ) → a negligible function chosen after the adversary; the extractor family is chosen before it; reason: the order of the statement
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Corollary 7.5, pp.52–53 (game: Definition 7.4, p.52)

import Definitions.Def_QubitTracking_MSAdv

set_option autoImplicit false

namespace QubitTracking

/-- **Corollary 7.5** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Corollary 7.5, pp.52–53; `n_e = n`). Let
`n(λ) ≥ λ` and `m₀(λ) = m₁(λ) = m(λ) ≥ λ` be polynomials. There is an efficient extractor `ℰ_H` with
access to `sk` and the register `𝐌` such that for any efficient adversary `𝒜` in the game of
Definition 7.4 (stage-0 oracle on `S^⊥ + u`, stage-1 oracle on `T + v`) with
`Pr[DualMultiStageSearchMonogamy(𝒜, 1^λ) ≠ ⊥] = ε′(λ)` an inverse polynomial and
`Pr[… = 1]/Pr[… ≠ ⊥] = 1 − ε(λ)`, running `ℰ_H^{𝒜¹_M}` on `𝐌` conditioned on `𝒜⁰_M` not aborting outputs
`x`, the Hadamard-basis measurement result on the anchor, with probability at least
`1 − 2√2 ε^{1/2} − negl(λ)`:
`𝔼[Tr(Π_eq ℰ_H^{𝒜¹_M} ρ_𝐌 (ℰ_H^{𝒜¹_M})† Π_eq) | 𝒜⁰_M does not abort] ≥ 1 − 2√2 ε^{1/2} − negl(λ)`,
`Π_eq = ∑_x H^{⊗n}|x⟩⟨x|H^{⊗n} ⊗ |x⟩⟨x|_𝐗`. Furthermore `ℰ_H^{𝒜¹_M}` only makes black-box access to
`𝒜¹_M` (up to `BeforeSplit`) and acts on `𝐌`.

**Formalization Note** As in `lemma_7_1`. -/
theorem corollary_7_5 (n m : ℕ → ℕ) (hn : PPADSIS.SubexpSIS.PolyBounded n)
    (hm : PPADSIS.SubexpSIS.PolyBounded m) (hnl : ∀ l, l ≤ n l ∧ l ≤ m l) :
    ∃ E : (l : ℕ) → BBExt (n l) (n l) (m l) (m l) (n l), BBEfficient E ∧
      ∀ A : (l : ℕ) → MSAdv (n l) (n l) (m l) (m l), MSEfficient A .dual →
        (∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧
          ∀ l, (1 : ℝ) ≤ (p l : ℝ) * (A l).notAbortProb .dual) →
        ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
          ∀ l, 1 - 2 * Real.sqrt 2 * Real.sqrt ((A l).lossGivenNotAbort .dual) - ν l ≤
            (E l).hadSucc (A l) .dual := by sorry

end QubitTracking
