-- Prove2me | Theorems.Thm_SYKLearn_lemma_4_8
-- name    : SYKLearn.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:17:29.728945+00:00
-- url     : https://prove2.me/theorems/256e1029-b308-437c-a724-adba3fde5648
-- title:
--   Lemma 4.8 — the moment bounds survive the direction error: $\mathbb E_{\mathcal D_{\rm init}}\delta\ge\mu/2$, $\mathbb E_{\mathcal D_{\rm init}}\delta^2\le2C_2$
-- statement:
--   There is a universal constant $C_2>0$ such that for every $\beta>0$ there are $\mu>0$, $C_\beta$ and $n_0$ such that for every even $n\ge n_0$ there is an event $E$ of the couplings with $\Pr_g[E]\ge1-C_\beta/n$ on which:
--
--   1. the bounds of Lemma 4.6 hold: $\mathbb E_{\delta\sim\mathcal D}\delta\ge\mu$ and $\mathbb E_{\delta\sim\mathcal D}\delta^2\le C_2$;
--   2. for every unit vector $\hat d$ with $\|\hat d-g/\|g\|_2\|_2\le1/m$, with the candidate Hamiltonian $\tilde H=\sigma_n\sqrt m\sum_I\hat d_I\Gamma_I$, $\alpha=\|g\|_2/(\sigma_n\sqrt m)$, and $\mathcal D_{\rm init}$ the law of Experiment 1 with measured Hamiltonian $\tilde H$ and input state $\rho_{\beta\alpha}(\tilde H)$,
--   $$\mathbb E_{\delta\sim\mathcal D_{\rm init}}\delta\ge\mu/2,\qquad \mathbb E_{\delta\sim\mathcal D_{\rm init}}\delta^2\le2C_2 .$$
--
--   So the experiment run with the learned Hamiltonian satisfies the hypotheses of Lemma 4.5, uniformly over all accurate directions.
--
--   **Formalization Note** The page refers to "the event $\mathcal E$ of Lemma 4.6" and to direction accuracy $\eta\le a/m$ with a small absolute constant $a$; the event and its constants are restated here, and the accuracy $1/m$ covers every $a\le1$.
--
--   Differences from the source:
--   - generalization: the Majorana operators ψ_i of the paper's fixed representation on ℂ^{2^{n/2}} → every Hermitian CAR family Q.γ of a SYKFastMix.FastMixing.Model; reason: the statement is invariant under unitary conjugation, and every CAR family in dimension 2^{n/2} is unitarily equivalent to the paper's, so it specializes to the paper's operators
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
--   - encoding: D, the distribution of δ when Experiment 1 is run with the true Gibbs state and the rescaled true Hamiltonian H/α (p.37) → energyLaw Q.γ (α⁻¹ • H_g) (gibbs H_g β) with α = ‖g‖₂/(σ_n√m); reason: this is Lemma 4.1's law for that experiment, written with spectral projections
--   - generalization: successful direction recovery with accuracy η ≤ a/m, a a sufficiently small absolute constant → every unit d̂ with ‖d̂ − g/‖g‖₂‖₂ ≤ 1/m; reason: covers every accuracy a/m with a ≤ 1; the proof uses only ‖Δ‖ ≤ ασ_n m η = O(n^{−3/2})
--   - reading: “Under the event E of Lemma 4.6” (with the constants µ, C₂ of Lemma 4.6, C₂ enlarged if necessary) → ∃ C₂, µ, E with Lemma 4.6's bounds on E together with the conclusion; reason: the lemma is about Lemma 4.6's event and constants; restating them in one statement is the only way to refer to them
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 4.8, p.38

import Mathlib
import Definitions.Def_SYKLearn_Experiment

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Lemma 4.8**, p.38 (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK Hamiltonians*,
STOC 2027 submission, held file sha256 5d7d199a…). Let `D_init` be the initial ideal experiment
yielding the score `AvgScore_ρ̃`. Under the event `E` of Lemma 4.6 and successful direction recovery
in Theorem 3.1 with accuracy `η ≤ a/m`, `E_{δ∼D_init} δ ≥ µ/2`, `E_{δ∼D_init} δ² ≤ 2C₂`.

**Formalization Note.** The event `E` of Lemma 4.6 and its constants `C₂, µ` are restated here
(existentially, with the bounds of Lemma 4.6 on `E`), since the lemma is about them; `C₂` may be
enlarged, as the proof says. "Successful direction recovery with accuracy `η ≤ a/m`" is: `d̂` is a
unit vector with `‖d̂ − g/‖g‖₂‖₂ ≤ 1/m`; this covers every accuracy `η ≤ a/m` with `a ≤ 1` (the
page's `a` is a small absolute constant). The candidate Hamiltonian is `H̃ = σ_n√m Σ_I d̂_I Γ_I`,
`α = ‖g‖₂/(σ_n√m)`, and `D_init` is the law of Experiment 1 with measured Hamiltonian `H̃` and input
`ρ̃ = ρ_{βα}(H̃)` (physical Gibbs state). `D` is as in Lemma 4.6. `Q.J = 1`; every CAR family. -/
theorem lemma_4_8 :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ β : ℝ, 0 < β → ∃ μ : ℝ, 0 < μ ∧ ∃ Cβ : ℝ, ∃ n₀ : ℕ,
      ∀ (N : ℕ) (Q : Model N), n₀ ≤ N → Q.J = 1 →
        ∃ E : Set (Disorder N), disorderLaw Q Eᶜ ≤ ENNReal.ofReal (Cβ / N) ∧
          ∀ w ∈ E,
            (μ ≤ ∫ δ, δ ∂(energyLaw Q.γ
                (((cnorm w / (sigma N * Real.sqrt (m N)))⁻¹ : ℝ) • hamiltonian Q w : Mat _)
                (gibbs (hamiltonian Q w) β)) ∧
              ∫ δ, δ ^ 2 ∂(energyLaw Q.γ
                (((cnorm w / (sigma N * Real.sqrt (m N)))⁻¹ : ℝ) • hamiltonian Q w : Mat _)
                (gibbs (hamiltonian Q w) β)) ≤ C₂) ∧
            ∀ dh : Disorder N, cnorm dh = 1 →
              cnorm (fun I => dh I - w I / cnorm w) ≤ (m N : ℝ)⁻¹ →
                μ / 2 ≤ ∫ δ, δ ∂(energyLaw Q.γ
                  ((sigma N * Real.sqrt (m N) : ℝ) • hamiltonian Q dh : Mat _)
                  (gibbs ((sigma N * Real.sqrt (m N) : ℝ) • hamiltonian Q dh : Mat _)
                    (β * (cnorm w / (sigma N * Real.sqrt (m N)))))) ∧
                ∫ δ, δ ^ 2 ∂(energyLaw Q.γ
                  ((sigma N * Real.sqrt (m N) : ℝ) • hamiltonian Q dh : Mat _)
                  (gibbs ((sigma N * Real.sqrt (m N) : ℝ) • hamiltonian Q dh : Mat _)
                    (β * (cnorm w / (sigma N * Real.sqrt (m N)))))) ≤ 2 * C₂ := by sorry

end SYKLearn
