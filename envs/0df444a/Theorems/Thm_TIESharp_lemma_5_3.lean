-- Prove2me | Theorems.Thm_TIESharp_lemma_5_3
-- name    : TIESharp.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:37:56.702428+00:00
-- url     : https://prove2.me/theorems/e01811e6-2a1c-4135-9954-4014d88dffb0
-- title:
--   Lemma 5.3 — joint mean-load inequality $\lambda\cdot\mu\le\frac T2(\sum_i\lambda_i+n\|\lambda\|_2)$
-- statement:
--   Let $n\ge2$, $t$ a nonnegative profile with Bounded-Square probabilities $q$, $\mu_i=\sum_jt_{ij}q_{ij}$ the mean loads and $T=\mathrm{OPT}(t)$. For every $\lambda\in[0,\infty)^n$,
--   $$\lambda\cdot\mu\ \le\ \frac T2\Big(\sum_i\lambda_i+n\|\lambda\|_2\Big).$$
--   Taking $\lambda$ equal to the selection probabilities of a maximum-load machine bounds the first term of the expected makespan.
--
--   Differences from the source: none.
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), Lemma 5.3, p.24

import Mathlib
import Definitions.Def_TIESharp_Nonneg
import Definitions.Def_TIESharp_opt
import Definitions.Def_TIESharp_bsProb

set_option autoImplicit false

namespace TIESharp

/-- **Lemma 5.3 (Joint mean-load inequality)** (Li, *Sharp Bounds for Truthful-in-Expectation
Scheduling*, arXiv:2611.05134, Lemma 5.3, p.24). Let `µ_i = Σ_j t_ij q_ij` (the Bounded-Square
mean loads) and `T = OPT(t)`. For every `λ ∈ [0, ∞)^n`,
`λ · µ ≤ (T/2) (Σ_i λ_i + n ‖λ‖₂)`.

**Formalization Note.** `n ≥ 2` is the standing assumption of §§3–5 (p.4). `‖λ‖₂` is
`√(Σ_i λ_i²)`; the weight vector is named `lam`. -/
theorem lemma_5_3 (n m : ℕ) (hn : 2 ≤ n) (t : Fin n → Fin m → ℝ) (ht : Nonneg t)
    (lam : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    ∑ i, lam i * ∑ j, t i j * bsProb t i j
      ≤ opt t / 2 * (∑ i, lam i + n * Real.sqrt (∑ i, lam i ^ 2)) := by sorry

end TIESharp
