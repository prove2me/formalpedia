-- Prove2me | Theorems.Thm_QubitTracking_lemma_6_20
-- name    : QubitTracking.lemma_6_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:33:20.968914+00:00
-- url     : https://prove2.me/theorems/b00dcb04-80bf-4fdd-9d38-9d88b8e9fc59
-- title:
--   Lemma 6.20 — at BeforeSplit the $b_0$ branches are nearly orthogonal: $\mathrm{Tr}(|+\rangle\langle+|_{\mathbf B}\rho)\le 2^{-m_0}+2\sqrt2\,\varepsilon^{1/2}+\mathrm{negl}$
-- statement:
--   Let $n(\lambda)\ge\lambda$, $n_e$, $m_0$, $m_1$ be polynomials. Take any efficient adversary $\mathcal A$ in the multi-stage game of Definition 6.1 with $\varepsilon'(\lambda)=\Pr[\mathsf{MultiStageSearchMonogamy}(\mathcal A,1^\lambda)\ne\bot]$ an inverse polynomial and $\Pr[\cdot=1]/\Pr[\cdot\ne\bot]=1-\varepsilon(\lambda)$. Let $|\psi\rangle$ be the state of the key register (🔑), the anchor and $\mathbf L\mathbf M\mathbf R\mathbf B$ at BeforeSplit conditioned on $\mathcal A^0_M$ not aborting, with $\mathsf{sk}$ purified in the key register and $b_0$ purified in $\mathbf B$. Then
--   $$\mathrm{Tr}\big(|+\rangle\langle+|_{\mathbf B}\cdot|\psi\rangle\langle\psi|\big)\le\frac1{2^{m_0}}+2\sqrt2\,\varepsilon^{1/2}+\mathrm{negl}(\lambda),\qquad|+\rangle_{\mathbf B}=2^{-m_0/2}\sum_{b_0}|b_0\rangle.$$
--
--   It says that a successful adversary must already have recovered $b_0$ at BeforeSplit, which is what the extractor of Lemma 7.1 exploits.
--
--   Differences from the source:
--   - reading: an efficient adversary of the multi-stage game, with registers passed between parties (Definitions 6.1, 7.4, 7.8) → MSAdv: seven polynomial-size circuits on a finite set of qubit wires, register hand-offs as disjoint wire sets, the abort decision and the answers read from wires at the end; reason: the paper leaves the computational model of the parties informal; a party's ancillas are untouched wires and measurements are deferred, which changes no probability
--   - encoding: b₀ sampled uniformly, or purified in a register 𝐁 initialized to |+⟩ (Definition 6.1, step 3) → b₀ averaged uniformly; reason: b₀ only controls the oracle, so purification gives the same probabilities
--   - encoding: ε′(λ) any inverse polynomial → 1 ≤ p(λ)·ε′(λ) for a polynomially bounded p; reason: the same condition, written without division by p(λ) = 0
--   - encoding: the decomposition |ψ⟩ = ∑ α_{sk,x} 2^{-m₀/2}|sk⟩|x⟩|ψ^{sk}_{x,b₀}⟩|b₀⟩ → a description of the actual state; plusOverlap computes the left side for it; reason: the decomposition holds for every state of this form and is not a hypothesis
--   - reading: negl(λ) → a negligible function that may depend on the adversary; reason: standard meaning for efficient adversaries
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 6.20, p.48 (game: Definition 6.1, pp.32–33)

import Definitions.Def_QubitTracking_MSAdv

set_option autoImplicit false

namespace QubitTracking

/-- **Lemma 6.20** (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time*,
arXiv:2605.30732 (held version, sha256 bf98e5b5…), Lemma 6.20, p.48; game of Definition 6.1,
pp.32–33, with `n(λ) ≥ λ` and `n_e(λ), m₀(λ), m₁(λ)` polynomials). Take any efficient adversary `𝒜`
in the multi-stage monogamy-of-entanglement game of Definition 6.1 with
`Pr[MultiStageSearchMonogamy(𝒜, 1^λ) ≠ ⊥] = ε′(λ)` an inverse polynomial and
`Pr[… = 1]/Pr[… ≠ ⊥] = 1 − ε(λ)`. For the state `|ψ⟩_{🔑𝐋𝐌𝐑𝐁}` at `BeforeSplit` conditioned on `𝒜⁰_M`
not aborting (with `sk` purified in `🔑` and `b₀` in `𝐁`),
`Tr(|+⟩⟨+|_𝐁 · |ψ⟩⟨ψ|_{🔑𝐋𝐌𝐑𝐁}) ≤ 1/2^{m₀} + 2√2 ε^{1/2} + negl(λ)`,
`|+⟩_𝐁 = 2^{-m₀/2} ∑_{b₀} |b₀⟩_𝐁`.

**Formalization Note** The decomposition `|ψ⟩ = ∑ α_{sk,x} 2^{-m₀/2} |sk⟩|x⟩|ψ^{sk}_{x,b₀}⟩|b₀⟩` in the
statement describes the state and is not a hypothesis; `MSAdv.plusOverlap` computes the left side
for the actual state. "Inverse polynomial `ε′`" is `1 ≤ p(λ) ε′(λ)` for a polynomially bounded `p`.
The negligible function may depend on the adversary. -/
theorem lemma_6_20 (n ne m0 m1 : ℕ → ℕ) (hn : PPADSIS.SubexpSIS.PolyBounded n)
    (hne : PPADSIS.SubexpSIS.PolyBounded ne) (hm0 : PPADSIS.SubexpSIS.PolyBounded m0)
    (hm1 : PPADSIS.SubexpSIS.PolyBounded m1) (hnl : ∀ l, l ≤ n l)
    (A : (l : ℕ) → MSAdv (ne l) (n l) (m0 l) (m1 l)) (hA : MSEfficient A .search)
    (hε' : ∃ p : ℕ → ℕ, PPADSIS.SubexpSIS.PolyBounded p ∧
      ∀ l, (1 : ℝ) ≤ (p l : ℝ) * (A l).notAbortProb .search) :
    ∃ ν : ℕ → ℝ, PPADSIS.SubexpSIS.Negligible ν ∧
      ∀ l, (A l).plusOverlap ≤
        1 / (2 : ℝ) ^ (m0 l) + 2 * Real.sqrt 2 * Real.sqrt ((A l).lossGivenNotAbort .search) +
          ν l := by sorry

end QubitTracking
