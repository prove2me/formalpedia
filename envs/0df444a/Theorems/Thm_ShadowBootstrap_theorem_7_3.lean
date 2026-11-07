-- Prove2me | Theorems.Thm_ShadowBootstrap_theorem_7_3
-- name    : ShadowBootstrap.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:37.8286+00:00
-- url     : https://prove2.me/theorems/a6a25c4f-e30b-4f29-a0ce-946f0866039f
-- title:
--   Theorem 7.3 — infidelity $\le\epsilon$ w.p. $1-\delta$, $T = O(\frac d\epsilon\log\frac1\delta)$, $N = O([n^3+\log\frac1\epsilon]\log\frac1\delta)$, depth $O(\log n)$, $\tilde O(d)$ time
-- statement:
--   There are a constant $C$, a law on measurement schedules depending only on $(n, \epsilon, \delta)$, and one real-RAM program $P$ with rational literals and no randomness such that for every $n$, every $\epsilon \in (0,1)$ and every $\delta \in (0, 1/2)$, with $d = 2^n$ and $L = 1 + n + \log(1/\epsilon) + \log(1/\delta)$:
--
--   1. every schedule in the support consists of valid circuits over $\{H, S, CX\}$ of depth at most $C(\lfloor\log_2 n\rfloor + 1)$, with
--   $$N \le C\Big[n^3 + \log\frac1\epsilon\Big]\log\frac1\delta \quad\text{settings and}\quad T \le C\,\frac d\epsilon\log\frac1\delta\quad\text{copies};$$
--   2. on every count array of such a schedule, $P$ (reading $\epsilon$, $\delta$, the schedule and the per-setting histograms) halts within
--   $$C\,d\Big[\log\frac1\epsilon\log\frac1\delta + \log^2\frac1\delta\Big]L^C$$
--   steps, writes at most $C\,d\log(1/\delta)\,L^C$ cells, and outputs a unit vector $|\hat\psi\rangle$;
--   3. for every unit vector $|\psi\rangle \in \mathbb C^d$,
--   $$\Pr\Big[1 - |\langle\psi|\hat\psi\rangle|^2 \le \epsilon\Big] \ge 1 - \delta,$$
--   the probability being over the schedule and the independent single-copy outcomes of all its shots.
--
--   This is the paper's main result: sample-optimal nonadaptive single-copy pure-state tomography with $\tilde O(1)$ shallow Clifford settings and nearly linear post-processing from histograms.
--
--   Differences from the source:
--   - reading: there is a nonadaptive single-copy tomography algorithm → a law on schedules of {H, S, CX} circuits depending only on (n, ϵ, δ), with independent Born outcomes per shot, and one real-RAM program serving every n, ϵ, δ that reads only ϵ, δ, the schedule and the histograms; reason: nonadaptive: all settings fixed before any outcome; one program for all n so that the time bound is meaningful
--   - reading: time and working memory → unit-cost real RAM with exact √ (the published MatMulTimeLP.RealRAM), rational literals, no randomness, two-bank input; time = executed instructions, memory = distinct cells written; reason: the paper counts arithmetic operations and uses square roots; it names no machine
--   - reading: Õ(·) → ≤ C·f·L^C with L = 1 + n + log(1/ϵ) + log(1/δ); reason: p.4: Õ suppresses polylogarithmic factors in d, 1/ϵ and 1/δ; one constant for all parameters
--   - reading: Clifford depth O(log n) → valid layered {H, S, CX} circuits of depth ≤ C(⌊log₂ n⌋ + 1); reason: the gate set of §3.1; +1 because n = 1 needs depth ≥ 1
--   - generalization: the time, memory and unit-output bounds for the histograms that occur → on every count array of every schedule in the support; N counted with multiplicity; n = 0 included; reason: the paper's loops do not depend on the data and Eq. (13) always returns a unit vector
--   - encoding: per-basis outcome histograms → dense count arrays in index order (qubit 0 most significant) in the real cells, settings encoded in the index cells; reason: dictionaries with absent keys read as 0 are the same data
--   - encoding: Pr[·] ≥ 1 − δ → success probability in ℝ≥0∞ as a sum over schedules weighted by the law; log the natural logarithm; reason: bases of logarithms change constants only
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), Theorem 7.3, p.28, and its proof, p.29; Theorem 1.1, p.4

import Mathlib
import Definitions.Def_ShadowBootstrap_Schedule

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Theorem 7.3, p.28 (arbitrary confidence; Theorem 1.1, p.4, is its informal version): for any
`ϵ ∈ (0, 1)` and `δ ∈ (0, 1/2)` there is a nonadaptive single-copy tomography algorithm that
outputs a unit vector `|ψ̂⟩` with `Pr[1 − |⟨ψ|ψ̂⟩|² ≤ ϵ] ≥ 1 − δ`. Each measurement has Clifford depth
`O(log n)`, `T = O((d/ϵ) log(1/δ))` and `N = O([n³ + log(1/ϵ)] log(1/δ))`. Given per-basis outcome
histograms, classical post-processing takes `Õ(d[log(1/ϵ) log(1/δ) + log²(1/δ)])` time and
`Õ(d log(1/δ))` working memory.

**Formalization Note** The algorithm is a pair: a law on measurement schedules depending on
`(n, ϵ, δ)` only (nonadaptive: every setting and shot count is fixed before any outcome; never on
`ψ`), and one real-RAM program (rational literals, no randomness) serving every `n, ϵ, δ`, which
reads `ϵ, δ`, the encoded schedule and the dense per-setting histograms (`encodeData`, two-bank
input) and writes `|ψ̂⟩` as real and imaginary parts. One constant `C`, chosen before `n, ϵ, δ, ψ`,
bounds every resource. For every schedule in the law's support: every setting is a valid circuit
over `{H, S, CX}` of depth `≤ C(⌊log₂ n⌋ + 1)`; `N` (settings, with multiplicity) and `T` (total
shots, one fresh copy each) obey the bounds; and on **every** count array the program halts within
the time bound, writes at most the memory bound of cells, and outputs a unit vector. `Õ(f)` is
`≤ C·f·L^C` with `L = 1 + log₂ d + log(1/ϵ) + log(1/δ)` (p.4: "Õ(·) suppresses polylogarithmic
factors in d, 1/ϵ, and 1/δ"). The success probability is over the schedule law and the independent
Born outcomes, for every unit vector `ψ` (`successProb`, in `ℝ≥0∞`). `log` is the natural
logarithm; `n = 0` is included. -/
theorem theorem_7_3 :
    ∃ (C : ℝ) (law : (n : ℕ) → ℝ → ℝ → PMF (Schedule n)) (P : MatMulTimeLP.Program),
      RationalLiterals P ∧ NoRandom P ∧
      ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 / 2 →
        (∀ s ∈ (law n ε δ).support,
          (∀ st ∈ s, Circuit.IsValid st.circ ∧ (depth st.circ : ℝ) ≤ C * (Nat.log 2 n + 1)) ∧
          (s.length : ℝ) ≤ C * ((n : ℝ) ^ 3 + Real.log (1 / ε)) * Real.log (1 / δ) ∧
          (totalShots s : ℝ) ≤ C * (2 ^ n / ε) * Real.log (1 / δ) ∧
          ∀ h : Counts s,
            HaltsWithin P (encodeData [ε, δ] (dataOf s h))
              (C * 2 ^ n * (Real.log (1 / ε) * Real.log (1 / δ) + Real.log (1 / δ) ^ 2) *
                (1 + n + Real.log (1 / ε) + Real.log (1 / δ)) ^ C) ∧
            (cellsWritten P (encodeData [ε, δ] (dataOf s h)) : ℝ) ≤
              C * 2 ^ n * Real.log (1 / δ) * (1 + n + Real.log (1 / ε) + Real.log (1 / δ)) ^ C ∧
            IsUnitVec (dataOutput P [ε, δ] (dataOf s h))) ∧
        ∀ ψ : Bits n → ℂ, IsUnitVec ψ →
          ENNReal.ofReal (1 - δ) ≤ successProb (law n ε δ) ψ
            (fun s h => 1 - ‖braket ψ (dataOutput P [ε, δ] (dataOf s h))‖ ^ 2 ≤ ε) := by sorry

end ShadowBootstrap
