-- Prove2me | Theorems.Thm_ProdMixedTomo_theorem_1_8
-- name    : ProdMixedTomo.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:20.382854+00:00
-- url     : https://prove2.me/theorems/57ed954c-fe4e-4c68-8425-e370ee707258
-- title:
--   Theorem 1.8 — polynomial-time semi-agnostic learner for binary products with error $O(\mathrm{opt}\log(1/\mathrm{opt}))+\epsilon$
-- statement:
--   There are a universal constant $C>0$ and one classical program $P$ such that for every $n$, every distribution $p$ on $\{0,1\}^n$, every $\epsilon>0$, $\delta>0$ and every
--   $$
--   N\ \ge\ C\cdot X\cdot(\log(2+X))^C,\qquad X=\frac{n^2\max\{1,\log(1/\delta)\}}{\epsilon^2},
--   $$
--   when $P$ is run on input $(n,N,\epsilon,\delta)$ and $N$ i.i.d. samples from $p$:
--   1. on every input of size $N$ and every run, $P$ halts within $C(N+1)^C$ steps;
--   2. except with probability $\delta$, its output $\hat q\in\mathcal P_n$ satisfies
--   $$
--   d_{\mathrm{tv}}(p,\hat q)\ \le\ C\,g(\mathrm{opt})+\epsilon,\qquad \mathrm{opt}=\inf_{q\in\mathcal P_n}d_{\mathrm{tv}}(q,p),
--   $$
--   with $g(t)=t\max\{1,\log(1/t)\}$, $g(0)=0$.
--
--   This resolves the paper's open question on near-optimal efficient robust learning of product distributions, and is the learner the tomography algorithm calls.
--
--   Differences from the source:
--   - reading: "with high probability", "sample complexity N = poly(n, 1/ϵ)" → failure ≤ δ for an input δ > 0 with N ≥ C·X·(log(2 + X))^C, X = n²·max{1, log(1/δ)}/ϵ²; reason: the proof (p.23) runs O(log(1/δ)) blocks of Õ(n²/a²) samples and selects with failure δ/2 (reading R6); the bound is poly(n, 1/ϵ) at every fixed δ, so it implies the printed claim
--   - encoding: "an algorithm", "runs in poly(N) time" → an admissible program of the measuring real RAM (Def_ProdMixedTomo_Machine) halting within ⌊C·(N + 1)^C⌋ steps on every run; reason: the paper names no machine (unit-cost real RAM, rational literals, no √, floor or eigensolver); N + 1 because every run needs a step and N may be 0
--   - reading: O(opt log(1/opt)) + ϵ → C·g(opt) + ϵ with g(t) = t·max{1, log(1/t)}, g(0) = 0; reason: the log convention, p.13
--   - encoding: "outputs a q̂ ∈ P_n" → output vector clipped to [0,1]ⁿ, read as Bern(·); reason: P_n is parametrized by mean vectors in [0,1]ⁿ
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 1.8, p.6 (PDF p.8); proof from Theorem 4.5, pp.22–23 (PDF pp.24–25)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Machine

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Theorem 1.8, p.6 (PDF p.8). There is a semi-agnostic learner for binary product distributions
with sample complexity `N = poly(n, 1/ϵ)` and computational complexity `poly(N)` that outputs
`q̂ ∈ P_n` with `d_tv(p, q̂) ≤ O(opt log(1/opt)) + ϵ` with high probability, where
`opt = inf_{q ∈ P_n} d_tv(q, p)`.

**Formalization Note.** Reading: "with high probability" is failure `≤ δ` for an input `δ > 0`,
with `N ≥ Õ(n² log(1/δ)/ϵ²) = C·X·(log(2+X))^C`, `X = n² max{1, log(1/δ)}/ϵ²` (the proof's rate,
p.23; it is `poly(n, 1/ϵ)` at every fixed `δ`). `opt log(1/opt)` is `g(opt) = opt·max{1, log(1/opt)}`,
`g(0) = 0`. One classical program and one `C` before all data; `p` is an arbitrary distribution
on `{0,1}ⁿ`; `poly(N)` is `C·(N + 1)^C` steps on every input and run. -/
theorem theorem_1_8 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧ IsClassical P ∧
    ∀ (n N : ℕ) (ϵ δ : ℝ) (p : Cube n → ℝ), 0 < ϵ → 0 < δ → IsDist p →
      otilde C ((n : ℝ) ^ 2 * logPlus (1 / δ) / ϵ ^ 2) ≤ N →
      (∀ S : Fin N → Cube n, ∀ s ∈ cReach P (classicalInput n N ϵ δ S)
          ⌊C * ((N : ℝ) + 1) ^ C⌋₊, s.halted = true) ∧
      sampleFail P n N ϵ δ p ⌊C * ((N : ℝ) + 1) ^ C⌋₊
          (fun s => s.halted = false ∨ C * gErr (optP p) + ϵ < dtv p (outBern n s)) ≤
        ENNReal.ofReal δ := by sorry

end ProdMixedTomo
