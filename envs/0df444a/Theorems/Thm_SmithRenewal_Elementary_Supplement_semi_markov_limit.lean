-- Prove2me | Theorems.Thm_SmithRenewal_Elementary_Supplement_semi_markov_limit
-- name    : SmithRenewal.Elementary.Supplement.semi_markov_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:56:01.316536+00:00
-- url     : https://prove2.me/theorems/74ae8711-083d-427e-9348-34d205eb2530
-- title:
--   Theorem (unnumbered, §2.2) — semi-Markov limiting state probability, including infinite-mean and transient cases
-- statement:
--   Consider Smith's countable semi-Markov process, with an arbitrary initial entry distribution $\alpha$ at time zero, transition probabilities $p_{ij}$, and pair-dependent finite nonnegative waits $T_{ij}$ that are not almost surely zero on active edges. Fix a target state $A_\mu$. Let $m_\mu=\sum_\nu p_{\mu\nu}\mathbb E T_{\mu\nu}$ be its expected holding time, $Q_\mu$ the probability of ever entering it in finite time (including the initial entry), and $l_\mu$ its mean elapsed time between successive entries when started there.
--
--   Assume $m_\mu<\infty$ and, when the target is persistent, that its entry-return duration law is nonperiodic. Then
--
--   $$
--   \lim_{t\to\infty}\mathbb P_\alpha\{x_t\in A_\mu\}=
--   \begin{cases}
--   Q_\mu m_\mu/l_\mu,& A_\mu\text{ persistent and }l_\mu<\infty,\\
--   0,&l_\mu=\infty\text{ or }A_\mu\text{ transient}.
--   \end{cases}
--   $$
--
--   This companion theorem identifies the limiting probability of occupying a target state from an arbitrary initial entry law. It is independent of the proof of the published elementary renewal theorem. It assumes neither irreducibility nor positive recurrence, finite means at other states, a density, or certain first entry.
--
--   **Formalization Note** The constructed path uses half-open sojourn intervals and a cemetery continuation after any accumulation of transition epochs. Zero-duration waits and self-transitions remain allowed. The recurrence mean is elapsed time, with non-return assigned infinity. Nonperiodicity is a condition on the return-time law, not on the embedded chain's discrete period. The limit is taken along real times and is expressed in the extended nonnegative reals; the finite-mean ratio and both zero cases are retained as three conjunctive clauses.
--
--   Differences from the source:
--   - encoding: countably many states A₀, A₁, … → an arbitrary countable type with measurable singletons; reason: the countable discrete sigma-algebra makes exactly the same state events measurable, including finite state spaces
--   - encoding: fresh successive choices of states and edge-dependent waits → independent product random tapes followed by recursive state selection; reason: each used coordinate is fresh at its step, so the joint next-state/wait law is pᵢⱼ Ωᵢⱼ and visited states remain Markov dependent
--   - encoding: nonnegative, certainly finite waits, not a.s. zero on active edges → probability laws on ℝ≥0 with mass at zero less than one on active edges; reason: finite nonnegative samples represent all a.s. finite laws; inactive-edge auxiliary laws are unused and no finite-mean requirement is imposed there
--   - encoding: an entry into some state at time zero, with probability Q_μ of ever entering the target → any initial PMF α, with Q_μ computed as the probability of a finite-index target entry including index zero; reason: every countable initial distribution is a PMF and every finite transition index has finite elapsed time; Q_μ is allowed to be below one
--   - reading: nonperiodic entry events and a separate zero limit for transient states → the nonperiodicity premise is required only for persistent targets and concerns elapsed return durations on a common lattice through zero; reason: the p. 261 paragraph treats transience first, then applies the p. 259 renewal periodicity convention only to persistent target entry cycles
--   - reading: continue the countable construction indefinitely, with no global nonexplosion premise → occupation is the union of finite-index half-open holding intervals, with a cemetery continuation if epochs accumulate; reason: this makes the source path prescription total without excluding explosive paths; at ordinary epochs it selects the state after all zero-time transitions
--   - encoding: the ratio Q_μm_μ/l_μ, zero for infinite l_μ or a transient state → extended nonnegative expectations and three conjunctive limit clauses, with non-return duration ∞; reason: this retains both infinite-return-mean and transient zero conclusions without converting infinity to a default real value; return times count elapsed duration and include self-transitions
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §2.2, p. 261, Theorem (unnumbered)

import Mathlib
import Definitions.Def_SmithRenewal_Elementary_Supplement_SemiMarkov

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SmithRenewal.Elementary.Supplement

/-- Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283
(1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §2.2, p. 261 (PDF 19),
Theorem (unnumbered). Companion theorem; not used in the proof of the published goal.

**Formalization Note** A countable discrete state space and arbitrary initial entry law
are retained. The nonperiodicity premise applies to the elapsed return-time law only for
persistent targets. The three clauses include the recurrent ratio, infinite-mean zero,
and transient zero cases. The model uses half-open sojourn intervals and the minimal
cemetery continuation at an accumulation of transition epochs. All means and probabilities
are extended nonnegative reals; no finite-mean condition is imposed at other states. -/
theorem semi_markov_limit {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : SemiMarkov S) (α : PMF S) (μ : S)
    (h_nonperiodic : Persistent M μ → Nonperiodic M μ)
    (h_mean : meanWait M μ < ∞) :
    (Persistent M μ →
      Tendsto (occupation M α μ) atTop
        (𝓝 (entryProbability M α μ * meanWait M μ / meanReturn M μ))) ∧
    (meanReturn M μ = ∞ → Tendsto (occupation M α μ) atTop (𝓝 0)) ∧
    (¬ Persistent M μ → Tendsto (occupation M α μ) atTop (𝓝 0)) := by sorry

end SmithRenewal.Elementary.Supplement
