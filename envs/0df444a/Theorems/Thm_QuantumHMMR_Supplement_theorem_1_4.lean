-- Prove2me | Theorems.Thm_QuantumHMMR_Supplement_theorem_1_4
-- name    : QuantumHMMR.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:19:27.919068+00:00
-- url     : https://prove2.me/theorems/5c982872-5712-42b2-ba8f-f1bfca530032
-- title:
--   Theorem 1.4 — an adaptive unitary $t$-design of depth $\mathrm{poly}(n,t,\log(1/\varepsilon))$ with error $\frac{2t(t-1)}{2^n}+\varepsilon$ that $O(nt)$ forward queries distinguish from Haar
-- statement:
--   This is the separation of polynomial-order adaptive unitary designs from pseudorandom unitaries.
--
--   Let $n\ge 64$ and let $t$ be an integer with $1\le t\le 2^{n/4-4}$. Write $\mu_H$ for the Haar measure on $n$-qubit unitaries and, for a probability law $\nu$ on $n$-qubit unitaries, $\delta_t(\nu,\mu_H)$ for the largest advantage with which an adaptive $t$-query algorithm (any number of ancillas, any final two-outcome measurement) distinguishes $U\sim\nu$ from $U\sim\mu_H$ (Definition 3.1, Eq. (6)). Then, for every $0<\varepsilon\le 1/2$, there is an adaptive unitary $t$-design in depth $\mathrm{poly}(n,t,\log(1/\varepsilon))$ with error
--   $$\delta_t(\nu,\mu_H)\le\frac{2t(t-1)}{2^n}+\varepsilon,$$
--   and yet an efficient quantum algorithm using $O(nt)$ forward queries and $\mathrm{poly}(n,t)$ time distinguishes it from Haar with constant advantage.
--
--   Precisely: there are a uniform polynomial-time family of tests $D_{n,t}$, constants $P,k$ (the depth polynomial), $C_q$ (the query constant) and $c>0$ such that for every $n\ge 64$, every integer $1\le t\le 2^{n/4-4}$ and every $0<\varepsilon\le1/2$ there is a probability law $\nu$ on $n$-qubit matrices with
--
--   1. almost every $U\sim\nu$ cleanly implemented (ancillas start and end in $|0\rangle$) by a circuit of one- and two-qubit gates, with depth and number of ancillas at most $P\,(n+t+\log(1/\varepsilon))^k$;
--   2. $\delta_t(\nu,\mu_H)\le \frac{2t(t-1)}{2^n}+\varepsilon$;
--   3. $D_{n,t}$ uses at most $C_q\,n\,t$ copies of its input state, prepared by forward queries;
--   4. the acceptance probability of $D_{n,t}$ on copies of $U|+\rangle^{\otimes n}$ is at least $c$ larger under $U\sim\nu$ than under $U\sim\mu_H$.
--
--   The theorem shows that matching moments of the Haar measure up to any polynomial order, even against adaptive queries, does not give computational pseudorandomness: the design property is statistical and a polynomial-time learner breaks it.
--
--   **Formalization Note** $\delta_t$ is the mission's published $\mathbb R_{\ge0}\cup\{\infty\}$-valued `advantage`; $\mu_H$ is the published `haarLaw`; $|+\rangle^{\otimes n}$ is the published `uniformState`. Circuits are the published `ConstDepthUnitary.Circuit` (layers of one- and two-qubit gates with disjoint supports, depth = number of layers, no fan-out) and clean implementation is the published `CleanlyImplements`. The test family is the mission's `CopyTest` (gates $H,T,\mathrm{CNOT}$ and controlled rotations, deferred measurement), uniform via `IsUniformFamily` on the unary word $1^n01^t$, so its running time is polynomial in $n+t$. The power $2^{n/4-4}$ is a real power.
--
--   Differences from the source:
--   - generalization: for each $(n,t,\varepsilon)$ a design and an efficient distinguisher with constant advantage → one uniform family $D$ and constants $P,k,C_q,c$ chosen before $n,t,\varepsilon$ and the ensemble; reason: the proof's learner (Lemma 5.5, Proposition 5.8 with $L=2t$) depends only on $(n,t)$ and works for every FB ensemble, and $\mathrm{poly}$, $O(nt)$ and "constant" are universal; it specializes to the printed claim
--   - generalization: distinguishes with constant advantage → the signed difference (acceptance under $\nu$ minus acceptance under Haar) is at least $c$; reason: implies the absolute advantage $\ge c$
--   - reading: an adaptive unitary $t$-design in depth $\mathrm{poly}(n,t,\log(1/\varepsilon))$ → a law almost surely supported on unitaries with a clean standard-gate circuit whose depth and ancilla count are both at most $P(n+t+\log(1/\varepsilon))^k$; reason: the paper's circuits (the phase operator $F_a$ with clean work qubits, Lemma 5.1, and the walk on $\hat S$) are standard-gate circuits of polynomial size; bounding the ancillas keeps width from being traded for depth
--   - generalization: an efficient quantum algorithm using $O(nt)$ forward queries → a `CopyTest`: $K\le C_q\,n\,t$ parallel forward queries, each on the fixed input $|+\rangle^{\otimes n}$, followed by one circuit over $\{H,T,\mathrm{CNOT},\mathrm{CRot}\}$ with deferred measurement; reason: a distinguisher of this restricted form is in particular an efficient algorithm with $O(nt)$ forward queries, and the paper's learner (Lemma 5.5: every forward query on $|+\rangle^{\otimes n}$, Lemma 5.6, Proposition 5.8 with Gaussian elimination, all exact over $H,T,\mathrm{CNOT}$) has this form; it specializes to the printed claim
--   - encoding: $\delta_t$ in $[0,1]$ and the error $2t(t-1)/2^n+\varepsilon$ → `advantage` in $\mathbb R_{\ge0}\cup\{\infty\}$ compared with `ENNReal.ofReal` of the error; reason: Lean convention; the error is positive so nothing is lost
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45e466107510463e2073f1a980be809e6d66218750afd88a9828844f20), Theorem 1.4, p.5; proof in §5, pp.16–22 (Lemmas 5.1, 5.4, 5.5, Proposition 5.8, proof of Theorem 1.4 p.22) and Appendices A–C, pp.30–33; QPT model §3, p.11; δ_t Definition 3.1, Eq. (6), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QAlgorithms_Defs_Fourier
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_CleanlyImplements
import Definitions.Def_QuantumHMMR_advantage
import Definitions.Def_QuantumHMMR_CopyTest
import Definitions.Def_QuantumHMMR_IsUniformFamily

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45 MeasureTheory

namespace QuantumHMMR.Supplement

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

/-- **Theorem 1.4** (separating adaptive unitary designs from pseudorandom unitaries;
Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*,
arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.5; proof in §5, pp.16–22, and
Appendices A–C). Let `n ≥ 64` and `1 ≤ t ≤ 2^{n/4−4}` be an integer. For every `0 < ε ≤ 1/2`
there exists an adaptive unitary `t`-design in depth `poly(n, t, log(1/ε))` with error
`2t(t−1)/2ⁿ + ε`, and yet an efficient quantum algorithm using `O(nt)` forward queries and
`poly(n, t)` time distinguishes it from Haar with constant advantage.

The Lean statement: there are a uniform polynomial-time family `D` of copy tests indexed by
`(n, t)` (given the unary word `1ⁿ 0 1ᵗ`), constants `P, k` (the depth polynomial), `Cq` (the query
constant) and `c > 0` such that for every `n ≥ 64`, every integer `t` with `1 ≤ t ≤ 2^{n/4−4}` and
every `0 < ε ≤ 1/2` there is a probability law `ν` on `n`-qubit matrices with:
1. almost every `U ∼ ν` is cleanly implemented (ancillas start and end in `|0⟩`) by a circuit of
   one- and two-qubit gates (no fan-out) of depth and ancilla count at most
   `P (n + t + log(1/ε))^k`;
2. `δ_t(ν, μ_H) ≤ 2t(t−1)/2ⁿ + ε`;
3. `D (n, t)` uses at most `Cq · n · t` copies;
4. the acceptance of `D (n, t)` on copies of `U|+⟩^{⊗n}` is at least `c` larger under `U ∼ ν` than
   under `U ∼ μ_H`.

**Formalization Note** `δ_t` is the published `ℝ≥0∞`-valued `QuantumHMMR.advantage` (supremum over
every adaptive `t`-query algorithm with any number of ancillas and every effect); `μ_H` is the
published `haarLaw`. `|+⟩^{⊗n}` is the published `QAlgorithms.uniformState (Qubits n)`. The circuit
model is the published `ConstDepthUnitary.Circuit` on wires `Fin n ⊕ Fin w` (data first, ancillas
second), restricted to standard gates, with depth the number of layers. `2^{n/4−4}` is a real power.
`D`, `P`, `k`, `Cq`, `c` are chosen before `n`, `t`, `ε` and `ν`. -/
theorem theorem_1_4 :
    ∃ D : (p : ℕ × ℕ) → CopyTest p.1,
      IsUniformFamily (fun p : ℕ × ℕ => List.replicate p.1 true ++ false :: List.replicate p.2 true)
        (fun p => p.1) D ∧
      ∃ P : ℝ, ∃ k : ℕ, ∃ Cq c : ℝ, 0 < c ∧
      ∀ n : ℕ, 64 ≤ n → ∀ t : ℕ, 1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4 - 4) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ ν : Measure (QMat n), IsProbabilityMeasure ν ∧
          (∀ᵐ U ∂ν, ∃ w : ℕ, ∃ C : ConstDepthUnitary.Circuit (Fin n ⊕ Fin w),
            C.IsStandard ∧ ConstDepthUnitary.CleanlyImplements C U ∧
            (C.depth : ℝ) ≤ P * ((n : ℝ) + t + Real.log (1 / ε)) ^ k ∧
            (w : ℝ) ≤ P * ((n : ℝ) + t + Real.log (1 / ε)) ^ k) ∧
          advantage t ν (haarLaw n) ≤
            ENNReal.ofReal (2 * (t : ℝ) * ((t : ℝ) - 1) / 2 ^ n + ε) ∧
          ((D (n, t)).K : ℝ) ≤ Cq * n * t ∧
          c ≤ (∫ U, (D (n, t)).accept (act U (uniformState (Qubits n))) ∂ν) -
            ∫ U, (D (n, t)).accept (act U (uniformState (Qubits n))) ∂haarLaw n := by sorry

end QuantumHMMR.Supplement
