-- Prove2me | Theorems.Thm_WildeQIT_Schumacher_theorem_11_10_1
-- name    : WildeQIT.Schumacher.theorem_11_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T18:36:37.545131+00:00
-- url     : https://prove2.me/theorems/03320743-14bd-4217-b47e-66266ad8163a
-- title:
--   Theorem 11.10.1 (Fannes–Audenaert Inequality), case split and universal bound
-- statement:
--   Let $\rho,\sigma$ be density operators on a Hilbert space $\mathcal H$ of finite dimension $\dim(\mathcal H)$, and suppose $\frac12\|\rho-\sigma\|_1 \le \varepsilon \in [0,1]$. Write $H$ for the quantum entropy and $h_2$ for the binary entropy (base 2). Then
--
--   1. if $\varepsilon \in [0, 1-1/\dim(\mathcal H)]$,
--   $$
--   |H(\rho)-H(\sigma)| \le \varepsilon\log[\dim(\mathcal H)-1] + h_2(\varepsilon);
--   $$
--   2. otherwise $|H(\rho)-H(\sigma)| \le \log\dim(\mathcal H)$;
--   3. in all cases (the universal bound)
--   $$
--   |H(\rho)-H(\sigma)| \le \varepsilon\log\dim(\mathcal H) + h_2(\varepsilon).
--   $$
--
--   The inequality turns a trace-distance bound into an entropy bound, the step by which converse theorems pass from error criteria to rates.
--
--   **Formalization Note** $\mathcal H$ has standard basis indexed by a finite type, so $\dim(\mathcal H)$ is its cardinality; $H$ is the published `QAlgorithms.vnEntropy`, $h_2$ is `WildeQIT.binaryEntropy`, $\|\cdot\|_1$ is `WildeQIT.traceNorm`. When $\dim(\mathcal H)=1$, $\log[\dim(\mathcal H)-1]$ is Lean's $\log_2 0 = 0$; then case 1 forces $\varepsilon = 0$ and both sides vanish. The same theorem is also drafted in the series' AFW mission (`WildeQIT.AFW.fannes_audenaert`).
--
--   Differences from the source: none.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.10.1, eqs. (11.236)–(11.237), p. 357

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_binaryEntropy

namespace WildeQIT.Schumacher

/-- **Theorem 11.10.1 (Fannes–Audenaert Inequality)** (Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, p. 357, eqs. (11.236)–(11.237)): "Let `ρ, σ ∈ D(H)` and suppose that
`½‖ρ − σ‖₁ ≤ ε ∈ [0, 1]`. Then
`|H(ρ) − H(σ)| ≤ ε log[dim(H) − 1] + h₂(ε)` if `ε ∈ [0, 1 − 1/dim(H)]`, and `log dim(H)` else.
Putting these together, a universal bound is `|H(ρ) − H(σ)| ≤ ε log dim(H) + h₂(ε)`."

The three conjuncts are the two cases of (11.236) and the universal bound (11.237).

**Formalization Note.** `H` has standard basis indexed by the finite type `ι`, so
`dim(H) = card ι`; `D(H)` is `WildeQIT.IsDensityOperator`, `‖·‖₁` is `WildeQIT.traceNorm`,
`H(·)` is the published `QAlgorithms.vnEntropy` and `h₂` is `WildeQIT.binaryEntropy`, all in bits.
When `dim(H) = 1`, `log[dim(H) − 1]` is Lean's `logb 2 0 = 0`; the first case then has `ε = 0`
and both sides are `0`. -/
theorem theorem_11_10_1 {ι : Type} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hσ : WildeQIT.IsDensityOperator σ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hdist : WildeQIT.traceNorm (ρ - σ) / 2 ≤ ε) :
    (ε ≤ 1 - 1 / (Fintype.card ι : ℝ) →
        |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤
          ε * Real.logb 2 ((Fintype.card ι : ℝ) - 1) + WildeQIT.binaryEntropy ε) ∧
    (1 - 1 / (Fintype.card ι : ℝ) < ε →
        |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤ Real.logb 2 (Fintype.card ι)) ∧
    |QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy σ| ≤
      ε * Real.logb 2 (Fintype.card ι) + WildeQIT.binaryEntropy ε := by sorry

end WildeQIT.Schumacher
