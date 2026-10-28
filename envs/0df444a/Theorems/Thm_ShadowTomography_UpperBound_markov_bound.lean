-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_markov_bound
-- name    : ShadowTomography.UpperBound.markov_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:05:37.237373+00:00
-- url     : https://prove2.me/theorems/3466dd92-e90a-428c-9e45-3ac982414da2
-- title:
--   Proof of Theorem 2, p. 17 — Markov bound Tr(F_tρ*_t) ≤ Tr(E_jρ_t)q/((Tr(E_jρ_t)+ε/4)q) for entangled ρ*_t
-- statement:
--   Let $\sigma$ be a mixed state on $q\ge1$ registers, possibly correlated or entangled across the registers, let $E$ be a two-outcome measurement on one register, and let $\varepsilon>0$. Let $\bar\sigma$ be the average one-register marginal of $\sigma$ and $a=\mathrm{Tr}(E\bar\sigma)$. Let $F_{+}$ apply $E$ to each of the $q$ registers and accept iff at least $(a+\varepsilon/4)q$ invocations accept, and $F_{-}$ accept iff at most $(a-\varepsilon/4)q$ invocations accept. Then
--
--   $$
--   \mathrm{Tr}(F_{+}\sigma) \le \frac{a\,q}{(a+\varepsilon/4)\,q}, \qquad \mathrm{Tr}(F_{-}\sigma)\le \frac{(1-a)\,q}{(1-a+\varepsilon/4)\,q}.
--   $$
--
--   In the proof of Theorem 2, $\sigma=\rho^*_t$, $\bar\sigma=\rho_t$ and $F_\pm$ is the postselection measurement $F_t$; the bound shows that each postselection step shrinks the success probability $p_t$ by a factor $1-\Omega(\varepsilon)$, whatever the correlations of $\rho^*_t$.
--
--   **Formalization Note** The fractions are kept exactly as printed (the factors $q$ are not cancelled). $q\ge1$ is required because the average marginal divides by $q$. The paper's "$=1-\Omega(\varepsilon)$" tail is not part of the statement; the bookkeeping quantity $p_t$ is not formalized.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 17, proof of Theorem 2 (definition of F_t; the two Markov displays)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Proof of Theorem 2, p. 17 (Markov claim).** Let `σ` be any (possibly entangled) state on
`q ≥ 1` registers, `E` a two-outcome measurement, `ε > 0`, and `a = Tr(E σ_avg)` where `σ_avg` is
the average one-register marginal of `σ`. Then the measurement accepting iff at least
`(a + ε/4) q` invocations of `E` accept has acceptance probability at most `a q / ((a + ε/4) q)`
on `σ`, and the one accepting iff at most `(a - ε/4) q` accept has acceptance probability at most
`(1 - a) q / ((1 - a + ε/4) q)`. -/
theorem markov_bound {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ) (q : ℕ)
    (σ : Matrix (Fin q → n) (Fin q → n) ℂ) (ε : ℝ)
    (hE : IsEffect E) (hσ : WildeQIT.IsDensityOperator σ) (hq : 1 ≤ q) (hε : 0 < ε) :
    (ampAtLeast E q ((E * avgMarginal σ).trace.re + ε / 4) * σ).trace.re ≤
        (E * avgMarginal σ).trace.re * q / (((E * avgMarginal σ).trace.re + ε / 4) * q) ∧
    (ampAtMost E q ((E * avgMarginal σ).trace.re - ε / 4) * σ).trace.re ≤
        (1 - (E * avgMarginal σ).trace.re) * q /
          ((1 - (E * avgMarginal σ).trace.re + ε / 4) * q) := by sorry

end ShadowTomography.UpperBound
