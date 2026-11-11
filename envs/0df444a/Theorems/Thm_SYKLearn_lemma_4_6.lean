-- Prove2me | Theorems.Thm_SYKLearn_lemma_4_6
-- name    : SYKLearn.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:25.657206+00:00
-- url     : https://prove2.me/theorems/6579c54f-60b2-4e5b-8029-c1fded77f41f
-- title:
--   Lemma 4.6 — moment bounds on $\mathcal D$: $\mathbb E\delta\ge\mu(\beta)$, $\mathbb E\delta^2\le C_2$ with probability $1-O(1/n)$
-- statement:
--   Let $\mathcal D$ be the law of the energy difference in Experiment 1 run on the true Gibbs state $\rho_\beta(H_g)$ with measured Hamiltonian $H_g/\alpha$, where $\alpha=\|g\|_2/(\sigma_n\sqrt m)$. There is a universal constant $C_2>0$ such that for every $\beta>0$ there are $\mu=\mu(\beta)>0$, $C_\beta$ and $n_0$ such that for every even $n\ge n_0$ there is an event $E$ of the couplings with $\Pr_g[E]\ge1-C_\beta/n$ on which
--
--   $$\mathbb E_{\delta\sim\mathcal D}\,\delta\ge\mu,\qquad \mathbb E_{\delta\sim\mathcal D}\,\delta^2\le C_2 .$$
--
--   The first moment is proportional to the thermal energy and the second to the size of the commutators $[H,\psi_i]$; together they feed Lemma 4.5.
--
--   **Formalization Note** $C_2$ is chosen before $\beta$; $\mu$, $C_\beta$ and $n_0$ after.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
--   - encoding: D, the distribution of δ when Experiment 1 is run with the true Gibbs state and the rescaled true Hamiltonian H/α (p.37) → energyLaw Q.γ (α⁻¹ • H_g) (gibbs H_g β) with α = ‖g‖₂/(σ_n√m); reason: this is Lemma 4.1's law for that experiment, written with spectral projections
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 4.6, p.37 (proof pp.37–38)

import Mathlib
import Definitions.Def_SYKLearn_Experiment

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 4.6 (Moment bounds on D)**, p.37 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning
SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). For every fixed `β > 0` and
sufficiently large `n`, there is an event `E(g)` depending only on the SYK couplings, with
`Pr_g[E(g)] ≥ 1 − O(1/n)` on which `E_{δ∼D} δ ≥ µ`, `E_{δ∼D} δ² ≤ C₂`, where `µ = µ(β) > 0` and
`C₂` is a universal constant.

**Formalization Note.** `D` (p.37) is the law of Experiment 1 run with the true Gibbs state
`gibbs H_g β` and the rescaled true Hamiltonian `H_g/α` as measured Hamiltonian,
`α = ‖g‖₂/(σ_n√m)`. `C₂` is chosen before `β`; `µ`, the `O(1/n)` constant `C_β` and the threshold
`n₀` after `β`. `E` is a set of couplings whose complement has outer measure `≤ C_β/N`. `Q.J = 1`;
every CAR family. -/
theorem lemma_4_6 :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ β : ℝ, 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ Cβ : ℝ, ∃ n₀ : ℕ,
      ∀ (N : ℕ) (Q : Model N), n₀ ≤ N → Q.J = 1 →
        ∃ E : Set (Disorder N), disorderLaw Q Eᶜ ≤ ENNReal.ofReal (Cβ / N) ∧
          ∀ w ∈ E,
            μ ≤ ∫ δ, δ ∂(energyLaw Q.γ
              (((cnorm w / (sigma N * Real.sqrt (m N)))⁻¹ : ℝ) • hamiltonian Q w : Mat _)
              (gibbs (hamiltonian Q w) β)) ∧
            ∫ δ, δ ^ 2 ∂(energyLaw Q.γ
              (((cnorm w / (sigma N * Real.sqrt (m N)))⁻¹ : ℝ) • hamiltonian Q w : Mat _)
              (gibbs (hamiltonian Q w) β)) ≤ C₂ := by sorry

end SYKLearn
