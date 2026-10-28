-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_theorem_2
-- name    : ShadowTomography.UpperBound.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:46:01.003008+00:00
-- url     : https://prove2.me/theorems/7b3070cb-5452-4c3a-8cde-5321980ae41d
-- title:
--   Theorem 2 (Shadow Tomography Theorem) — Õ(log(1/δ) log⁴M log D/ε⁵) copies estimate all Tr(E_iρ) to ±ε
-- statement:
--   **Shadow tomography.** Let $\rho$ be an unknown $D$-dimensional mixed state and $E_1,\dots,E_M$ known two-outcome measurements. The task is to output numbers $b_1,\dots,b_M\in[0,1]$ with $|b_i-\mathrm{Tr}(E_i\rho)|\le\varepsilon$ for all $i$, with success probability at least $1-\delta$, via a measurement of $\rho^{\otimes k}$ with $k=k(D,M,\varepsilon,\delta)$ as small as possible.
--
--   **Theorem.** There is a universal constant $C>0$ such that for all $D\ge0$, $M\ge2$, $0<\varepsilon\le1/2$ and $0<\delta\le1/2$ there is a number of copies
--
--   $$
--   k \le C\,\frac{\log D}{\varepsilon}\left(\frac{\log\log D+\log\frac1\varepsilon}{\varepsilon^2}\right)^{2}\log^4 M\,\Big(\log\log M+\log\log D+\log\frac1\varepsilon+\log\frac1\delta\Big)
--   $$
--
--   with the following property: for every list of two-outcome measurements $E_1,\dots,E_M$ on $\mathbb C^D$ there is a measurement of $\rho^{\otimes k}$, together with outputs $b_1,\dots,b_M\in[0,1]$ for each outcome, such that for every $D$-dimensional mixed state $\rho$,
--
--   $$
--   \Pr\big[\,|b_i-\mathrm{Tr}(E_i\rho)|\le\varepsilon\ \text{for all } i\in[M]\,\big]\ \ge\ 1-\delta .
--   $$
--
--   The bound is $\tilde O\big(\frac{\log(1/\delta)}{\varepsilon^5}\log^4M\log D\big)$: polylogarithmic in both the number of measurements and the dimension.
--
--   **Formalization Note** This is the explicit bound of the last display of the proof of Theorem 2 (p. 19), i.e. the $\varepsilon^{-5}$ form proved in §5; the printed $\varepsilon^{-4}$ form of p. 3 relies on an external online-learning algorithm and is not stated. Quantifier order: $C$ first; $k$ depends only on $(D,M,\varepsilon,\delta)$; the measurement and outputs depend on the $E_i$ but not on $\rho$. Added hypotheses: $M\ge2$ (at $M=1$, $\log M=0$ forces $k=0$, and no zero-copy output estimates one nontrivial $\mathrm{Tr}(E_1\rho)$ to within $1/4$), $\varepsilon\le1/2$ and $\delta\le1/2$ (they keep both $\log\log$-containing factors positive; for $\varepsilon\ge1/2$ outputting $1/2$ is trivially correct). No hypothesis on $D$ is needed: $D=0$ has no state and at $D=1$ the state is known. All logarithms are natural (`Real.log`), including inside $\log\log$. The measurement is a POVM with a finite outcome type, and "probability" is the Born-rule probability of the success event.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 2, Problem 1; p. 3, Theorem 2; p. 15, restatement in §5; p. 19, last display of the proof of Theorem 2

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM

open scoped ComplexOrder

namespace ShadowTomography.UpperBound

/-- **Theorem 2 (Shadow Tomography Theorem), in the explicit form proved in §5.** There is a
universal constant `C` such that for all `D`, `M ≥ 2`, `0 < ε ≤ 1/2` and `0 < δ ≤ 1/2` there is a
number of copies
`k ≤ C (log D/ε) ((log log D + log(1/ε))/ε²)² log⁴ M (log log M + log log D + log(1/ε) + log(1/δ))`
such that for every list of two-outcome measurements `E 0, …, E (M-1)` on `ℂ^D` there is a
measurement of `ρ^{⊗k}` (independent of `ρ`) whose outcome yields numbers `b_i ∈ [0, 1]` with
`|b_i - Tr(E_i ρ)| ≤ ε` for all `i` simultaneously, with probability at least `1 - δ`, for every
`D`-dimensional mixed state `ρ`. -/
theorem theorem_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D M : ℕ) (ε δ : ℝ), 2 ≤ M → 0 < ε → ε ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∃ k : ℕ, (k : ℝ) ≤ C * (Real.log D / ε) *
            ((Real.log (Real.log D) + Real.log (1 / ε)) / ε ^ 2) ^ 2 * Real.log M ^ 4 *
            (Real.log (Real.log M) + Real.log (Real.log D) + Real.log (1 / ε) +
              Real.log (1 / δ)) ∧
          ∀ E : Fin M → Matrix (Fin D) (Fin D) ℂ, (∀ i, IsEffect (E i)) →
            ∃ (Ω : Type) (_ : Fintype Ω) (P : POVM Ω (Fin k → Fin D)) (b : Ω → Fin M → ℝ),
              (∀ ω i, b ω i ∈ Set.Icc (0 : ℝ) 1) ∧
              ∀ ρ : Matrix (Fin D) (Fin D) ℂ, WildeQIT.IsDensityOperator ρ →
                1 - δ ≤ P.prob (tensorPow ρ k)
                  (fun ω => ∀ i, |b ω i - ((E i) * ρ).trace.re| ≤ ε) := by sorry

end ShadowTomography.UpperBound
