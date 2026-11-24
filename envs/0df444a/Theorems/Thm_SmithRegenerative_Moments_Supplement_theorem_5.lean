-- Prove2me | Theorems.Thm_SmithRegenerative_Moments_Supplement_theorem_5
-- name    : SmithRegenerative.Moments.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:47:50.801811+00:00
-- url     : https://prove2.me/theorems/a2735a35-a2bd-485e-99ad-3b3a9442c71a
-- title:
--   Theorem 5 — S.M. limiting state probability (corrected: aperiodicity)
-- statement:
--   Let an S.M. process freshly enter its initial state $z$ at time zero, and fix a state $\mu$. Suppose its return law is aperiodic and the unconditional mean wait $m_{\mu\mu}$ is finite. If $Q_\mu(z)$ is its probability of finite first entry and $l_\mu$ its extended mean first return from fresh entry into $\mu$, then
--   $$\lim_{t\to\infty}P_z(x_t=\mu)=Q_\mu(z)\frac{m_{\mu\mu}}{l_\mu}.$$
--   The limit is zero for $l_\mu=\infty$. Countably many states, defective waits, zero hitting probabilities and nonirreducible models are retained; regularity is not a hypothesis. The result converts regeneration limits into state probabilities.
--
--   Differences from the source:
--   - correction: The entry event is “not periodic”. → The return law is aperiodic.; reason: Section 3·3 says the joint event-period and aperiodicity cases are not exhaustive. Return span 2 and first delay 1 satisfy the literal printed premise but give oscillating occupation. The proof invokes Corollary 2·1, which requires an aperiodic cycle law. Excluded cases are lattice return laws with misaligned delay spans; see DISPROOF.md.
--   - correction: A positive-integer state process; the text asserts that its regularity condition ensures nonexplosion. → The minimal Markov-renewal realization, killed at explosion, with hitting restricted to finite indexed entries.; reason: The Bernoulli-divergence argument on p. 21 fails for unbounded epsilon. The explicit completion preserves every finite path and excludes unspecified post-explosion resurrection; no nonexplosion premise is added. See DISPROOF.md.
--   - encoding: Real time and the paper’s distribution-function notation. → Probability measures with explicit mass at infinity and real-time limits; lattice sampling alone uses natural indices.; reason: Preserve defective laws, infinite means and the exact asymptotic domain without total-function defaults.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 20, Theorem 5

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Supplement_SMProcess

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory Filter Topology

/-- Smith (1955), Theorem 5, p. 20, (4·2·1), corrected aperiodicity reading.
Formalization Note: a fresh entry at zero is built into SMProcess. No regularity,
proper-wait or recurrence assumption. Interpret 'not periodic' as aperiodic RETURN
law, as required by the cited Corollary 2·1. Literally excluding only the joint event
period of §3·3 is insufficient (deterministic alternating waits 1, first entry 1).
Occupation is the minimal process killed at explosion, retaining every finite path
and all defective waits; arbitrary post-explosion resurrection is not specified. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω]
    (M : SMProcess Ω) (z μ : ℕ)
    (haper : Aperiodic (M.returnLaw μ)) (hm : M.S.m μ μ < ⊤) :
    (M.l μ = ⊤ → Tendsto (fun t : ℝ => (M.P z (M.inState μ t)).toReal)
      atTop (𝓝 0)) ∧
    (M.l μ ≠ ⊤ → Tendsto (fun t : ℝ => (M.P z (M.inState μ t)).toReal)
      atTop (𝓝 ((M.Q z μ).toReal * (M.S.m μ μ).toReal / (M.l μ).toReal))) := by sorry

end SmithRegenerative.Moments.Supplement
