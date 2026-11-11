-- Prove2me | Theorems.Thm_ProdMixedTomo_corollary_3_3
-- name    : ProdMixedTomo.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:12.714824+00:00
-- url     : https://prove2.me/theorems/0a3e9ddf-1d72-4347-b645-45fa7ffe3fcb
-- title:
--   Corollary 3.3 — polynomial-time agnostic tomography of product mixed states from single-copy single-qubit measurements, error $O(\mathrm{opt}\log(1/\mathrm{opt}))+\epsilon$
-- statement:
--   There are a universal constant $C>0$ and one program $L$ of the measuring machine such that for every $n$, every $\epsilon>0$, $\delta>0$, every $n$-qubit density matrix $\rho$ and every
--   $$
--   N\ \ge\ C\cdot X\cdot(\log(2+X))^C,\qquad X=\frac{n^2\max\{1,\log(1/\delta)\}}{\epsilon^2},
--   $$
--   when $L$ is run on input $(n,N,\epsilon,\delta)$ with access to copies of $\rho$ only through single-copy, single-qubit (product, possibly adaptive) measurements:
--   1. on every run, $L$ halts within $C(N+1)^C$ steps having consumed at most $N$ copies;
--   2. except with probability $\delta$, the product mixed state $\hat\pi\in\mathcal M_n$ it outputs satisfies
--   $$
--   d_{\mathrm{tr}}(\rho,\hat\pi)\ \le\ C\,g(\mathrm{opt})+\epsilon,\qquad \mathrm{opt}=\inf_{\pi\in\mathcal M_n}d_{\mathrm{tr}}(\pi,\rho),
--   $$
--   with $g(t)=t\max\{1,\log(1/t)\}$, $g(0)=0$.
--
--   This is the paper's main result (the detailed form of Theorem 1.2): the first polynomial-time semi-agnostic learner for product mixed states with a dimension-independent error guarantee.
--
--   Differences from the source:
--   - reading: "Let ϵ, δ > 0. Let ρ be an n-qubit density matrix. There is an algorithm …" → one program L and one C chosen before n, N, ϵ, δ and ρ; n, N, ϵ, δ are inputs; reason: read as Theorem 1.2 states it; ∀ρ ∃ algorithm is trivial (output ρ's nearest product state) (reading R4)
--   - encoding: "an algorithm, using only single-copy, single-qubit measurements, which given N ≥ N₀ copies … runs in poly(N) time" → an admissible program of the measuring real RAM, accessing ρ only through measure, halting within ⌊C·(N + 1)^C⌋ steps with at most N copies consumed on every run; reason: the paper names no machine (unit-cost real RAM, rational literals, no √, floor or eigensolver); N + 1 because every run needs a step and N may be 0
--   - reading: Õ(n² log(1/δ)/ϵ²) → C·X·(log(2 + X))^C with X = n²·max{1, log(1/δ)}/ϵ²; reason: polylog of the printed argument (the stronger reading of Õ; the proofs give it)
--   - reading: d_tr(ρ, π̂) ≲ opt · log 1/opt + ϵ → d_tr(ρ, π̂) ≤ C·g(opt) + ϵ; reason: Theorem 1.2 writes O(opt log(1/opt)) + ϵ; the form with coefficient 1 on ϵ implies the ≲ form; log convention p.13
--   - encoding: "a description of a product state π̂" → output cells (b_j, λ_j) decoded as ⨂ⱼ((1 − λ̄ⱼ)P(bⱼ) + λ̄ⱼ(I − P(bⱼ))), always in M_n; reason: the output format of Algorithm 1 (line 12); the product state is a product mixed state
--   - encoding: "with probability at least 1 − δ" → the run law gives the set {not halted, or the bound fails} measure ≤ δ; reason: failure sets, not 1 − success
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Corollary 3.3, p.16 (PDF p.18); Theorem 1.2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_States
import Definitions.Def_ProdMixedTomo_TraceDistance
import Definitions.Def_ProdMixedTomo_Machine

open scoped ComplexOrder

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Corollary 3.3, p.16 (PDF p.18) (the detailed statement of Theorem 1.2). Let `ϵ, δ > 0` and let
`ρ` be an `n`-qubit density matrix. There is an algorithm, using only single-copy, single-qubit
measurements, which given `N ≥ N₀ = Õ(n² log(1/δ)/ϵ²)` copies of `ρ` runs in `poly(N)` time and
outputs, with probability at least `1 − δ`, a description of a product mixed state `π̂` with
`d_tr(ρ, π̂) ≲ opt · log 1/opt + ϵ`, where `opt = inf_{π ∈ M_n} d_tr(π, ρ)`.

**Formalization Note.** One program `L` of the measuring machine and one constant `C`, chosen
before `n, N, ϵ, δ, ρ`; `n, N, ϵ, δ` are inputs (`p[0], p[1], M[0], M[1]`) and `ρ` is reached only
through `measure` (single copy, product over qubits, adaptively chosen directions). On every run
`L` halts within `C·(N + 1)^C` steps having consumed at most `N` copies; the decoded output is
always in `M_n`. `Õ(X) = C·X·(log(2+X))^C` with `X = n² max{1, log(1/δ)}/ϵ²`; the error bound is
`C·g(opt) + ϵ` with `g(t) = t·max{1, log(1/t)}`, `g(0) = 0`. -/
theorem corollary_3_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ L : Program, Admissible L ∧
    ∀ (n N : ℕ) (ϵ δ : ℝ) (ρ : QMat n), 0 < ϵ → 0 < δ → IsDensity ρ →
      otilde C ((n : ℝ) ^ 2 * logPlus (1 / δ) / ϵ ^ 2) ≤ N →
      (∀ s ∈ Reach L ρ (learnerInput n N ϵ δ) ⌊C * ((N : ℝ) + 1) ^ C⌋₊,
          s.halted = true ∧ s.copies ≤ N) ∧
      runLaw L ρ (learnerInput n N ϵ δ) ⌊C * ((N : ℝ) + 1) ^ C⌋₊
          {s | s.halted = false ∨ C * gErr (optM ρ) + ϵ < dtr ρ (decodeState n s)} ≤
        ENNReal.ofReal δ := by sorry

end ProdMixedTomo
