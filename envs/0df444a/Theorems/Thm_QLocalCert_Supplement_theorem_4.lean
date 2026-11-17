-- Prove2me | Theorems.Thm_QLocalCert_Supplement_theorem_4
-- name    : QLocalCert.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:42:26.282584+00:00
-- url     : https://prove2.me/theorems/f975d9c6-06e3-40d1-94e6-d17550e90f40
-- title:
--   Theorem 4 — every $\mu$-round dMA protocol for $\mathrm{SYM}$ (and $\mathrm{SYM}_D$, $D\ge5$, $\mu\le D-4$) needs $\Omega(n^2/\mu)$ bits
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $\mu=\mu(n)\ge1$ be a round budget with $\mu(n)/n\to0$, and let $c,s$ satisfy $0\le s<c\le1$ and $2c-1>s$. Then there is $n_0$ such that for every $n\ge n_0$ and every identifier bound $U\ge n$:
--
--   1. every $\mu(n)$-round dMA protocol on $n$-node networks that decides $\mathrm{SYM}$ with completeness $c$ and soundness error $s$ using certificates of at most $b$ bits per node has
--   $$
--   b\ \ge\ C\,\frac{n^2}{\mu(n)};
--   $$
--   2. the same bound holds for every $\mu(n)$-round dMA protocol deciding $\mathrm{SYM}_D$, for every $D\ge5$ with $\mu(n)\le D-4$.
--
--   The protocols may use private randomness and public randomness (sampled after the certificates), unrestricted local computation and unrestricted message sizes. This extends the known one-round $\Omega(n^2)$ bound for symmetry to any number of rounds $\mu=o(n)$, and shows that the hardness persists under a radius bound.
--
--   **Formalization Note** The model is the published $\mu$-round dMA model of the mission; correctness is required on every connected graph with every identifier and port assignment. "Worst-case certificate size $b$" means that the protocol is correct with certificates of at most $b$ bits.
--
--   Differences from the source:
--   - generalization: Ω(n²/µ) for a fixed µ(n) and fixed c, s → one constant C > 0 before µ, c and s; reason: the proof's bound b > log₂|F_k|/(2µ) − 1 with log₂|F_k| ≥ (1 − o(1))k²/2 and k = Θ(n) does not depend on µ, c, s (pp.53–54); for fixed µ, c, s it is the printed statement
--   - generalization: identifier bound U = n^{O(1)} (§2.1, p.15) → every U ≥ n; reason: the fooling family uses identifiers 1, …, n only (p.53); polynomial U is a special case
--   - generalization: a known integer D with D ≥ 5 and µ ≤ D − 4 → every D, possibly depending on n, with D ≥ 5 and µ(n) + 4 ≤ D; reason: covers fixed D and the growing D(n) of p.54; for fixed D it is the printed statement
--   - encoding: µ = o(n) → µ(n)/n → 0 as n → ∞; reason: definition of little-o
--   - encoding: completeness c and soundness error s → hypotheses 0 ≤ s < c ≤ 1 and s < 2c − 1; reason: 0 ≤ s < c ≤ 1 is the model's standing assumption (Definition 7, p.16)
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), Theorem 4, p.6, restated p.52; proof pp.52–54

import Mathlib
import Definitions.Def_QLocalCert_DMA
import Definitions.Def_QLocalCert_Supplement_SYM

open Filter Topology
set_option autoImplicit false

namespace QLocalCert.Supplement

/-- **Theorem 4** (stated p.6, restated and proved p.52). "Let μ = μ(n) ≥ 1 satisfy μ = o(n). Every
μ-round dMA protocol for SYM with fixed completeness c and soundness error s satisfying 2c − 1 > s
has worst-case certificate size Ω(n²/μ) bits. The same bound holds for SYM_D whenever D ≥ 5 and
μ ≤ D − 4."

Source: B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), Theorem 4, p.6 and p.52; proof pp.52–54.

**Formalization Note.**
* The model is the published `μ`-round dMA model `QLocalCert.DMA n U (μ n)` with its correctness
  `DMA.Correct L b c s` (certificates of at most `b` bits per node; every connected graph on `Fin n`,
  every injective identifier map, every port numbering; private and public randomness with arbitrary
  laws, arbitrary state and message types). "Worst-case certificate size `b`" means: the protocol is
  correct with certificates of at most `b` bits.
* `μ : ℕ → ℕ` with `μ n ≥ 1` and `μ n / n → 0` (`μ = o(n)`).
* `Ω(n²/μ)` is one universal constant `C > 0` chosen before `μ`, `c`, `s`, and a threshold `n₀`
  chosen after them; for every `n ≥ n₀` and every identifier bound `U ≥ n`.
* The model's `0 ≤ s < c ≤ 1` (Definition 7, p.16) is assumed together with `2c − 1 > s`.
* `SYM_D`: for every `D` (possibly depending on `n`) with `D ≥ 5` and `μ n ≤ D − 4`. -/
theorem theorem_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℕ → ℕ, (∀ n, 1 ≤ μ n) →
      Tendsto (fun n : ℕ => (μ n : ℝ) / n) atTop (𝓝 0) →
      ∀ c s : ℝ, 0 ≤ s → s < c → c ≤ 1 → s < 2 * c - 1 →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ U : ℕ, n ≤ U →
          (∀ (P : DMA n U (μ n)) (b : ℕ), P.Correct SYM b c s →
            C * (n : ℝ) ^ 2 / (μ n : ℝ) ≤ b) ∧
          (∀ D : ℕ, 5 ≤ D → μ n + 4 ≤ D → ∀ (P : DMA n U (μ n)) (b : ℕ),
            P.Correct (SYMD D) b c s → C * (n : ℝ) ^ 2 / (μ n : ℝ) ≤ b) := by sorry

end QLocalCert.Supplement
