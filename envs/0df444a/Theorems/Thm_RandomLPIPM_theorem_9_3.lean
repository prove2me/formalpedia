-- Prove2me | Theorems.Thm_RandomLPIPM_theorem_9_3
-- name    : RandomLPIPM.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:44.991383+00:00
-- url     : https://prove2.me/theorems/46ea36d8-61cc-4838-a354-ee3940ae621d
-- title:
--   Theorem 9.3 — smoothed-divergence path following in $O((1+\max\{C,1\}\log(\mu_{\mathrm{start}}/\mu_{\mathrm{end}}))\log(n/\varepsilon))$ steps
-- statement:
--   Consider (LP) with $A$ of full row rank and both programs strictly feasible, $n\ge1$. Suppose the central path is $C$-Lipschitz in logarithmic coordinates on $[\mu_{\mathrm{end}},\mu_{\mathrm{start}}]$, $0<\mu_{\mathrm{end}}\le\mu_{\mathrm{start}}$. Given $\varepsilon\in(0,1/6]$ and a strictly feasible $x^0$ with $E_{\mu_{\mathrm{start}}}(x^0)\le\varepsilon$, Algorithm 1 returns $(\hat x,\hat\mu)$ with $\hat\mu=\mu_{\mathrm{end}}$, $\hat x$ strictly feasible and $E_{\mu_{\mathrm{end}}}(\hat x)\le\varepsilon$, using at most
--   $$K\Big(1+\max\{C,1\}\log\frac{\mu_{\mathrm{start}}}{\mu_{\mathrm{end}}}\Big)\log\frac n\varepsilon$$
--   projected-gradient evaluations, for an absolute constant $K$; each requires one linear system solve in $AX^2A^\top$.
--
--   This deterministic theorem converts a Lipschitz bound on the central path into an iteration bound; with $C=\sqrt n$ (true for every LP) it recovers the classical $\tilde O(\sqrt n)$ bound.
--
--   Differences from the source:
--   - encoding: an LP with n variables, log(n/ε) in the bound → hypothesis 1 ≤ n; reason: excludes the empty program, for which log(n/ε) is undefined
--   - encoding: projected gradient descent steps, each requiring O(1) linear system solves → the number of evaluations of line 7 of Algorithm 1 (each one application of P_x); reason: evaluations exceed steps by one per outer iteration, absorbed by the O; a bound on evaluations bounds the steps
--   - reading: Algorithm 1 returns (x̂, μ̂) → the run reaches the return state at some j, with s.μ = μ_end; reason: the Output line of Algorithm 1 is (x̂, μ_end)
--   - encoding: ‖d log x(μ) / d log μ‖_∞ ≤ C (Definition 9.1) → ∀ μ i ∃ g, HasDerivAt of t ↦ log x(e^t)_i at log μ with |g| ≤ C; reason: asserts differentiability instead of using a junk-valued derivative
--   - reading: the unsubscripted norm of E_μ (p.73) → the Euclidean norm; reason: Theorem 2.1 and Remark 1.2 write ‖·‖₂, and the proofs of Lemmas 9.5 and 9.7 use ℓ2
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 9.3, p.77 (proof pp.79–81)

import Mathlib
import Definitions.Def_RandomLPIPM_IsPrimalStrictFeas
import Definitions.Def_RandomLPIPM_IsDualStrictFeas
import Definitions.Def_RandomLPIPM_proximity
import Definitions.Def_RandomLPIPM_IsLogLipschitz
import Definitions.Def_RandomLPIPM_algo1Step
import Definitions.Def_RandomLPIPM_algo1Init
import Definitions.Def_RandomLPIPM_IsHalted

open Matrix

namespace RandomLPIPM

/-- **Theorem 9.3 (Smoothed-divergence path following).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Theorem 9.3, p.77 (proof pp.79–81).

Suppose the central path of (LP) is `C`-Lipschitz in logarithmic coordinates on `[μ_end, μ_start]`.
Given `ε ∈ (0, 1/6]` and a strictly feasible `x⁰` with `E_{μ_start}(x⁰) ≤ ε`, Algorithm 1 returns
`(x̂, μ̂)` with `x̂` strictly feasible to (LP) and `E_{μ_end}(x̂) ≤ ε`, using a total of
`O((1 + max{C, 1} log(μ_start/μ_end)) log(n/ε))` projected gradient descent steps; each step
requires `O(1)` linear system solves.

**Formalization Note.** The hypotheses are the standing assumptions of (LP) (p.4: `A` has full row rank, dual strictly feasible; primal strict feasibility is supplied by `x⁰`) and `0 < μ_end ≤ μ_start` (Definition 9.1), plus
`n ≥ 1` (an LP with at least one variable; `log(n/ε)` needs it). The run halts, its output is
`(s.x, s.μ)` with `s.μ = μ_end` (the Output line of Algorithm 1), and `s.solves` counts the line-7
evaluations: each is one projected-gradient evaluation `P_x∇Φ` (one linear system solve in `AX²Aᵀ`),
and there is one more evaluation than steps per outer iteration, which the `O` absorbs. The constant
`K` is absolute (chosen before all data). -/
theorem theorem_9_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ)
      (c : Fin n → ℝ), 1 ≤ n → A.rank = d → (∃ y, IsDualStrictFeas A c y) →
    ∀ C μend μstart ε : ℝ, 0 < μend → μend ≤ μstart → 0 < ε → ε ≤ 1 / 6 →
    ∀ x0 : Fin n → ℝ, IsPrimalStrictFeas A b x0 → proximity A b c μstart x0 ≤ ε →
    IsLogLipschitz A b c C μend μstart →
    ∃ j : ℕ,
      let s := (algo1Step A c μend ε C)^[j] (algo1Init x0 μstart)
      IsHalted s ∧
        (s.solves : ℝ) ≤ K * (1 + max C 1 * Real.log (μstart / μend)) * Real.log (n / ε) ∧
        IsPrimalStrictFeas A b s.x ∧ s.μ = μend ∧ proximity A b c μend s.x ≤ ε := by sorry

end RandomLPIPM
