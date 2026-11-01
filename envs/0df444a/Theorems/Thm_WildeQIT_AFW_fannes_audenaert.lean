-- Prove2me | Theorems.Thm_WildeQIT_AFW_fannes_audenaert
-- name    : WildeQIT.AFW.fannes_audenaert
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:16.074516+00:00
-- url     : https://prove2.me/theorems/9a21f5a0-d88c-4346-b983-b9d54e7763ea
-- title:
--   Theorem 11.10.1 (Fannes–Audenaert): $|H(\rho)-H(\sigma)| \le \varepsilon\log(d-1) + h_2(\varepsilon)$ for $\varepsilon \le 1-1/d$
-- statement:
--   Let $\rho,\sigma$ be density operators on a Hilbert space $\mathcal H$ of dimension $d$, and let $\varepsilon\in[0,1]$ with
--
--   $$
--   \tfrac12\|\rho-\sigma\|_1 \le \varepsilon .
--   $$
--
--   Write $H$ for the von Neumann entropy and $h_2$ for the binary entropy (base-2 logarithms). Then:
--
--   1. if $\varepsilon \in [0, 1 - 1/d]$,
--   $$
--   |H(\rho)-H(\sigma)| \le \varepsilon\log(d-1) + h_2(\varepsilon) ;
--   $$
--   2. if $\varepsilon > 1 - 1/d$,
--   $$
--   |H(\rho)-H(\sigma)| \le \log d ;
--   $$
--   3. in every case (the universal bound),
--   $$
--   |H(\rho)-H(\sigma)| \le \varepsilon\log d + h_2(\varepsilon) .
--   $$
--
--   This is the continuity of the von Neumann entropy with an explicit modulus in the trace distance. It turns error bounds of protocols, which are stated in trace distance, into bounds on entropies, as in converse proofs of coding theorems.
--
--   **Formalization Note** $\mathcal H$ is a finite index type with $d$ its cardinality; density operators are `WildeQIT.IsDensityOperator`, the trace norm is `WildeQIT.traceNorm`, $H$ is `QAlgorithms.vnEntropy` and $h_2$ is `WildeQIT.binaryEntropy`. The distance is bounded by $\varepsilon$, as on the page, not equal to it.
--
--   Differences from the source:
--   - encoding: at $d = 1$ the term $\varepsilon\log(d-1)$ has $\log 0$ → `Real.logb 2 0 = 0`; reason: at $d = 1$ the first case forces $\varepsilon = 0$, where the book's term is $0\cdot\log 0$, read as $0$; no instance changes.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.1, (11.236)–(11.237), p. 357

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_binaryEntropy

namespace WildeQIT.AFW

/-- Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 11.10.1
(Fannes–Audenaert Inequality), p. 357: "Let ρ, σ ∈ D(H) and suppose that ½∥ρ − σ∥₁ ≤ ε ∈ [0, 1].
Then the following inequality holds
|H(ρ) − H(σ)| ≤ ε log[dim(H) − 1] + h₂(ε) if ε ∈ [0, 1 − 1/dim(H)], and log dim(H) else. (11.236)
Putting these together, a universal bound is |H(ρ) − H(σ)| ≤ ε log dim(H) + h₂(ε). (11.237)"

The three conjuncts are the two cases of (11.236) and the universal bound (11.237).

**Formalization Note.** `H` is a finite index type `ι` with `dim(H) = card ι`; `D(H)` is
`WildeQIT.IsDensityOperator`, `∥·∥₁` is `WildeQIT.traceNorm`, `H(·)` is the von Neumann entropy
`QAlgorithms.vnEntropy` and `h₂` is `WildeQIT.binaryEntropy`, all with `log₂`. When
`dim(H) = 1`, `log[dim(H) − 1] = Real.logb 2 0 = 0`; the first case then forces `ε = 0`. -/
theorem fannes_audenaert {ι : Type} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdist : WildeQIT.traceNorm (ρ - σ) / 2 ≤ ε) :
    (ε ≤ 1 - 1 / (Fintype.card ι : ℝ) →
        |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤
          ε * Real.logb 2 ((Fintype.card ι : ℝ) - 1) + WildeQIT.binaryEntropy ε) ∧
    (1 - 1 / (Fintype.card ι : ℝ) < ε →
        |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤ Real.logb 2 (Fintype.card ι)) ∧
    |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤
      ε * Real.logb 2 (Fintype.card ι) + WildeQIT.binaryEntropy ε := by sorry

end WildeQIT.AFW
