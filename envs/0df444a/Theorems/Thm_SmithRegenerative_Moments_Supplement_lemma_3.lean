-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_Supplement_lemma_3
-- name    : SmithRegenerative.Moments.Supplement.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:48:39.073005+00:00
-- url     : https://prove2.me/theorems/69449293-6be1-45c4-ae50-4a9f09f501a9
-- title:
--   Lemma 3 — equal finite transition masses give equal hitting probabilities (corrected: completion)
-- statement:
--   Consider two regular S.M. realizations, possibly on different probability spaces, freshly entering the same initial label $z$. If their finite-transition masses agree for every pair of states,
--   $$p_{ij}^{(1)}G_{ij}^{(1)}([0,\infty))=p_{ij}^{(2)}G_{ij}^{(2)}([0,\infty)),$$
--   then
--   $$Q_\mu^{(1)}(z)=Q_\mu^{(2)}(z)\quad\hbox{for every }\mu.$$
--   Regularity is the source sequence condition (4·4·1). The finite hitting probabilities are derived from the stochastic realization, not assumed path expansions. This equality supplies the hitting-probability part of Theorem 6.
--
--   Differences from the source:
--   - correction: A positive-integer state process; the text asserts that its regularity condition ensures nonexplosion. → The minimal Markov-renewal realization, killed at explosion, with hitting restricted to finite indexed entries.; reason: The Bernoulli-divergence argument on p. 21 fails for unbounded epsilon. The explicit completion preserves every finite path and excludes unspecified post-explosion resurrection; no nonexplosion premise is added. See DISPROOF.md.
--   - reading: The two processes have the same initial state x₀ (no hypothesis on a transition at t = 0). → Both realizations freshly enter the common initial label z at time zero.; reason: (M1)–(M3) specify waits only after an entry, so the law of a residual first wait is not part of the source model; the proof's path probabilities (4·5·2) use the fresh-entry product p_{μν}Ω_{μν}(+∞) for every transition, including the first.
--   - encoding: Real time and the paper’s distribution-function notation. → Probability measures with explicit mass at infinity and real-time limits; lattice sampling alone uses natural indices.; reason: Preserve defective laws, infinite means and the exact asymptotic domain without total-function defaults.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 22, Lemma 3

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_SMProcess

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), Lemma 3, p. 22, (4·5·1).
Formalization Note: separate sample spaces; same fresh initial label z. Regularity
is exactly (4·4·1), without assuming its claimed nonexplosion consequence. Hitting
probabilities are computed from finite-time indexed entries, not assumed path sums.
The minimal killed convention also defines these quantities on explosive trajectories. -/
theorem lemma_3 {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (M₁ : SMProcess Ω₁) (M₂ : SMProcess Ω₂)
    (hr₁ : M₁.S.Regular) (hr₂ : M₂.S.Regular)
    (h : ∀ i j : ℕ, M₁.S.finiteMass i j = M₂.S.finiteMass i j)
    (z : ℕ) : ∀ μ : ℕ, M₁.Q z μ = M₂.Q z μ := by sorry

end SmithRegenerative.Moments.Supplement
