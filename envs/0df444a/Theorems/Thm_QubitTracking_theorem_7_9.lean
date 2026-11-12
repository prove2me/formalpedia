-- Prove2me | Theorems.Thm_QubitTracking_theorem_7_9
-- name    : QubitTracking.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:34:13.437625+00:00
-- url     : https://prove2.me/theorems/7bdef4df-87b9-4181-b462-37a8ed9eb6a1
-- title:
--   Theorem 7.9 — an efficient black-box extractor recovers $n$ EPR pairs with fidelity $1-O(\varepsilon^{1/4})$ in the multi-stage independent game
-- statement:
--   Let $n(\lambda)\ge\lambda$ and $m_0=m_1=m(\lambda)\ge\lambda$ be polynomials. There is an efficient extractor $\mathcal E$ with access to $\mathsf{sk}$ and the register $\mathbf M$ such that for any efficient adversary $\mathcal A$ in the multi-stage independent game of Definition 7.8 with $\Pr[\ne\bot]=\varepsilon'$ an inverse polynomial and $\Pr[=1]/\Pr[\ne\bot]=1-\varepsilon$, running $\mathcal E^{\mathcal A^1_M}$ on $\mathbf M$ conditioned on $\mathcal A^0_M$ not aborting extracts a state on $\mathbf A\mathbf X$ close to $n$ EPR pairs:
--   $$\mathbb E\big[\mathrm{Tr}(\langle\mathrm{EPR}|^{\otimes n}_{\mathbf A\mathbf X}\,\mathcal E^{\mathcal A^1_M}\rho\,(\mathcal E^{\mathcal A^1_M})^\dagger\,|\mathrm{EPR}\rangle^{\otimes n}_{\mathbf A\mathbf X})\,\big|\,\text{no abort}\big]\ge1-O(\varepsilon^{1/4}).$$
--   The extractor only makes black-box access to $\mathcal A^1_M$ and acts on $\mathbf M$.
--
--   This rigidity theorem is what the proof of Theorem 9.6 applies at the chosen pair of checkpoints.
--
--   Differences from the source:
--   - reading: an efficient adversary of the multi-stage game, with registers passed between parties (Definitions 6.1, 7.4, 7.8) → MSAdv: seven polynomial-size circuits on a finite set of qubit wires, register hand-offs as disjoint wire sets, the abort decision and the answers read from wires at the end; reason: the paper leaves the computational model of the parties informal; a party's ancillas are untouched wires and measurements are deferred, which changes no probability
--   - encoding: b₀ sampled uniformly, or purified in a register 𝐁 initialized to |+⟩ (Definition 6.1, step 3) → b₀ averaged uniformly; reason: b₀ only controls the oracle, so purification gives the same probabilities
--   - encoding: ε′(λ) any inverse polynomial → 1 ≤ p(λ)·ε′(λ) for a polynomially bounded p; reason: the same condition, written without division by p(λ) = 0
--   - reading: an efficient extractor with access to sk and the register 𝐌 that only makes black-box access to 𝒜¹_M and acts on 𝐌 → BBExt: an adversary-independent family of polynomially many ancilla gates and calls of 𝒜¹_M's unitary up to BeforeSplit (forward or inverted, possibly controlled), its oracle queries answered by circuits of the extractor, sk written on its ancillas; reason: the paper's extractors (compressed-oracle simulation in Lemma 7.1, controlled ℰ_S, ℰ_H and their reverses through Corollary 7.7 in Theorem 7.9) are of this form
--   - reading: Definition 7.8: θ₀ given 'to 𝒜⁰_M' and θ₁ 'to 𝒜¹_M' → θ₀ given to 𝒜¹_M and θ₁ to 𝒜²_M; reason: the named parties have already acted; the reduction in the proof of Theorem 8.4 (pp.58–59) gives θ₀ to 𝒜¹_M and θ₁ to 𝒜²_M
--   - reading: ≥ 1 − O(ε^{1/4}) (no negligible term printed) → ≥ 1 − C ε(λ)^{1/4} for all λ ≥ λ₀, with a constant C > 0 and a threshold λ₀ chosen after the extractor and before the adversary; reason: O(·) in a statement indexed by λ holds for all sufficiently large λ; the O-constant may depend on the fixed extractor only; the printed bound has no negligible term; the threshold is needed, since at λ = 0 the hypotheses allow m(0) = 0, n(0) = 1, and the adversary that hands the vessel to 𝒜⁰_L and does nothing else wins with certainty (ε = 0) while every extractor has EPR fidelity 1/4
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 7.9 and Definition 7.8, p.55

import Definitions.Def_QubitTracking_MSAdv

set_option autoImplicit false

namespace QubitTracking

/-- **Theorem 7.9** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Theorem 7.9 with Definition 7.8, p.55). Let
`n(λ) ≥ λ` and `m₀(λ) = m₁(λ) = m(λ) ≥ λ` be polynomials. There is an efficient extractor `ℰ` with
access to `sk` and the register `𝐌` such that for any efficient adversary `𝒜` in the
multi-stage independent monogamy-of-entanglement game of Definition 7.8 with
`Pr[MultiStageIndependentMonogamy(𝒜, 1^λ) ≠ ⊥] = ε′(λ)` an inverse polynomial and
`Pr[… = 1]/Pr[… ≠ ⊥] = 1 − ε(λ)`, running `ℰ^{𝒜¹_M}` on `𝐌` conditioned on `𝒜⁰_M` not aborting extracts
a state on `𝐗` close to `n` EPR pairs:
`𝔼[Tr(⟨EPR|^{⊗n}_𝐗 ℰ^{𝒜¹_M} ρ_𝐌 (ℰ^{𝒜¹_M})† |EPR⟩^{⊗n}_𝐗) | 𝒜⁰_M does not abort] ≥ 1 − O(ε^{1/4})`.
Furthermore `ℰ^{𝒜¹_M}` only makes black-box access to `𝒜¹_M` (up to `BeforeSplit`) and acts on `𝐌`.

**Formalization Note** Definition 7.8 says the challenger gives `θ₀` "to `𝒜⁰_M`" and `θ₁` "to
`𝒜¹_M`" after those parties have acted; read, as in the reduction of the proof of Theorem 8.4
(pp.58–59), as `θ₀` given to `𝒜¹_M` and `θ₁` to `𝒜²_M`. The EPR pairs pair the anchor with `𝐗`.
`1 − O(ε^{1/4})` is `≥ 1 − C ε^{1/4}` for a constant `C` fixed with the extractor, for all
sufficiently large `λ` (`λ ≥ λ₀`, the asymptotic meaning of `O(·)` in `λ`); as printed there is no
negligible term. The threshold is needed: at `λ = 0` the hypotheses allow `m(0) = 0` and `n(0) = 1`,
and an adversary whose `𝒜⁰_M` hands the vessel to `𝒜⁰_L` and does nothing else wins with certainty
(`ε = 0`, the answers being empty) while every extractor's EPR fidelity is `1/4 < 1`. -/
theorem theorem_7_9 (n m : ℕ → ℕ) (hn : PPADSIS.SubexpSIS.PolyBounded n)
    (hm : PPADSIS.SubexpSIS.PolyBounded m) (hnl : ∀ l, l ≤ n l ∧ l ≤ m l) :
    ∃ E : (l : ℕ) → BBExt (n l) (n l) (m l) (m l) (n l), BBEfficient E ∧
      ∃ C : ℝ, 0 < C ∧ ∃ l₀ : ℕ,
        ∀ A : (l : ℕ) → MSAdv (n l) (n l) (m l) (m l), MSEfficient A .indep →
          (∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧
            ∀ l, (1 : ℝ) ≤ (p l : ℝ) * (A l).notAbortProb .indep) →
          ∀ l ≥ l₀, 1 - C * ((A l).lossGivenNotAbort .indep) ^ (1 / 4 : ℝ) ≤
            (E l).eprSucc (A l) .indep := by sorry

end QubitTracking
