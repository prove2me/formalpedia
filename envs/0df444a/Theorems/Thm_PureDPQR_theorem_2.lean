-- Prove2me | Theorems.Thm_PureDPQR_theorem_2
-- name    : PureDPQR.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:43.063436+00:00
-- url     : https://prove2.me/theorems/f079603c-d825-4a5b-a150-13b4ab163df7
-- title:
--   Theorem 2, p.4 — a polynomial-time pure $\varepsilon$-DP algorithm with $\mathrm{err}_Q\le C\min\{1,\sqrt{\log(2d/\beta)\log(2k)/(N\varepsilon)}\}$ w.p. $1-\beta$
-- statement:
--   **Theorem 2.** There is a universal constant $C$ with the following property. Let $N\ge1$, $d\ge2$, $k\ge1$, $0<\varepsilon\le1$ and $0<\beta<\frac12$. There is a pure $\varepsilon$-differentially private algorithm (under replacement adjacency) such that on every histogram $h$ of mass $N$ and every public query table $\{q_i\}_{i\in[k]}\in[0,1]^{k\times d}$ it outputs $\hat p\in\Delta_d$ and
--
--   $$\Pr\Big\{\mathrm{err}_Q(\hat p,h)>C\min\Big\{1,\sqrt{\frac{\log(2d/\beta)\log(2k)}{N\varepsilon}}\Big\}\Big\}\le\beta .$$
--
--   Further, its running time is polynomial in $d,k,N$.
--
--   The algorithm is Algorithm 2 of the paper. The statement gives the $N^{-1/2}$ rate conjectured by Nikolov and Ullman for pure-DP statistical query release, with a polynomial-time mechanism.
--
--   **Formalization Note** All clauses are stated for Algorithm 2's output law `alg2Law`. One constant $C$, one time exponent $c$ and one admissible program $P$ of the machine of Remark 24 are chosen before all parameters; on every instance the law of $P$'s output equals `alg2Law h` and $P$ halts within $c(Ndk)^c$ steps on every tape. "Outputs $\hat p\in\Delta_d$" is `alg2Law h (Δ_d)ᶜ = 0`.
--
--   Differences from the source:
--   - reading: "there is a pure ε-differentially private algorithm" → every clause stated for Algorithm 2's output law alg2Law; reason: the paper proves Theorem 2 for Algorithm 2 (§6, p.25; proof, p.28); this implies the existential form
--   - reading: "the running time is in poly(d, k, N)" (model of Remark 24) → ∃ c : ℕ and one admissible program P of PureDPQR.Machine, chosen with C before all parameters, with programLaw P (goalInput …) = alg2Law h and P halting within c·(N·d·k)^c steps on every tape; reason: Remark 24 fixes the cost model; the law equality ties P to Algorithm 2 and forces a measurable output map; the machine computes Laplace and Bernoulli draws from uniforms, so it is no stronger than Remark 24's
--   - encoding: "it outputs p̂ ∈ Δ_d" → alg2Law h (stdSimplex ℝ (Fin d))ᶜ = 0; reason: the same claim about the output law
--   - encoding: adjacency h′ = h + e_a − e_b on ℕ^d → h′ + e_b = h + e_a; reason: no truncated subtraction; the same pairs
--   - encoding: Lap(κ) of rate κ → PrivLearn.Generic.laplace κ⁻¹ (scale parameter); reason: the published Laplace law is parametrized by its scale; same law
--   - encoding: probabilities; 1-based indices → ℝ≥0∞-valued measures; Fin d, Fin k, Fin (2k); reason: Lean conventions
--   - encoding: Algorithm 2, a randomized procedure → its output law alg2Law = Σ_y Q_h(y) δ_{D(y)}, with Q_h(y) the integral smoothed; reason: Z_j = B_j L_j has law (1−π)δ₀ + πLap(κ) and y given Z has law p_{h+Z}, so this is the law of the output
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Theorem 2, p.4 (PDF p.5); Algorithm 2, p.25; proof of Theorem 2 (§6.3) and Remark 24, p.28

import Mathlib
import Definitions.Def_PureDPQR_IsDP
import Definitions.Def_PureDPQR_errQ
import Definitions.Def_PureDPQR_alg2Law
import Definitions.Def_PureDPQR_Machine

namespace PureDPQR

/-- **Theorem 2**, p.4 (PDF p.5).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"There is a universal constant C with the following property. Let N ≥ 1, d ≥ 2, k ≥ 1, and
0 < ε ≤ 1, 0 < β < 1/2. There is a pure ε-differentially private algorithm (under replacement
adjacency) such that on every histogram h of mass N and every public query set {q_i}_{i∈[k]} ∈
[0, 1]^{k×d}, it outputs p̂ ∈ ∆d and satisfies
Pr{errQ(p̂, h) > C min{1, √(log(2d/β) log(2k)/(Nε))}} ≤ β. Further, the running time is in
poly(d, k, N)."

**Formalization Note.**
* The algorithm is the paper's Algorithm 2 (§6, p.25, "As our main algorithm, Algorithm 2 …"; the
  proof of Theorem 2, p.28, is for it). Every clause is stated for its output law `alg2Law`, which
  implies the existential form.
* Pure `ε`-DP under replacement adjacency is Definition 4 with `δ = 0` (`IsDP N d · ε 0`), over
  every adjacent pair in `H_{N,d}` and every Borel event of `ℝ^d`.
* "Outputs `p̂ ∈ Δ_d`" is `alg2Law h (Δ_d)ᶜ = 0`; the failure event is strict (`C·min{…} < errQ`).
* "The running time is in poly(d, k, N)" is read in the model of Remark 24 (p.28), encoded as the
  machine `PureDPQR.Machine`: one admissible program `P` and one `c : ℕ`, chosen with `C` before
  all parameters, such that on every instance the law of `P`'s output on the input `goalInput`
  equals `alg2Law h`, and `P` halts within `c·(N·d·k)^c` steps on every tape. The law equality
  ties `P` to Algorithm 2 (and forces a measurable output map). -/
theorem theorem_2 :
    ∃ C : ℝ, ∃ c : ℕ, ∃ P : Program, Admissible P ∧
      ∀ (N d k : ℕ) (ε β : ℝ), 1 ≤ N → 2 ≤ d → 1 ≤ k → 0 < ε → ε ≤ 1 → 0 < β → β < 1 / 2 →
        ∀ Q : Fin k → Fin d → ℝ, (∀ i j, Q i j ∈ Set.Icc (0 : ℝ) 1) →
          IsDP N d (alg2Law N d k ε β Q) ε 0 ∧
            ∀ h ∈ histograms N d,
              alg2Law N d k ε β Q h (stdSimplex ℝ (Fin d))ᶜ = 0 ∧
                alg2Law N d k ε β Q h {p | C * min 1 (Real.sqrt (Real.log (2 * d / β) *
                    Real.log (2 * k) / ((N : ℝ) * ε))) < errQ N Q p h} ≤ ENNReal.ofReal β ∧
                programLaw P d (goalInput N d k ε β Q h) = alg2Law N d k ε β Q h ∧
                ∀ ω : ℕ → ℝ, HaltsWithin P (goalInput N d k ε β Q h) (c * (N * d * k) ^ c) ω := by sorry

end PureDPQR
