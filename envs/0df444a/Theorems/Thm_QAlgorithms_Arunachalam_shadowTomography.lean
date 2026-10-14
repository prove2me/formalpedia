-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_shadowTomography
-- name    : QAlgorithms.Arunachalam.shadowTomography
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:54:21.613377+00:00
-- url     : https://prove2.me/theorems/fae6aff9-8b8f-463d-ac05-d3bee965009f
-- title:
--   Shadow tomography with poly(log m, log d, 1/ε, log(1/δ)) copies
-- statement:
--   This is Aaronson's shadow tomography theorem.
--
--   A two-outcome measurement on $\mathbb C^d$ is a POVM $\{E,\mathbb 1-E\}$ with $0\preceq E\preceq\mathbb 1$. A learner using $k$ copies of an unknown $d$-dimensional density matrix $\rho$ performs a measurement (a POVM $\{N_o\}_{o\in O}$ with finite outcome set $O$) on $\rho^{\otimes k}$ and outputs numbers $b(o)=(b_1(o),\dots,b_m(o))\in[0,1]^m$.
--
--   There is a polynomial $p$ in four variables such that for all $\varepsilon,\delta\in(0,1]$, all integers $m,d>0$ and all effects $E_1,\dots,E_m$ on $\mathbb C^d$ there exist $k\le p(\log m,\log d,1/\varepsilon,\log(1/\delta))$ and such a learner (depending on $m,d,\varepsilon,\delta$ and $E_1,\dots,E_m$, but not on $\rho$) with
--
--   $$
--   \Pr_{o\sim\{\operatorname{Tr}(N_o\rho^{\otimes k})\}}\Big[\ \forall i\in[m]:\ |\operatorname{Tr}(E_i\rho)-b_i(o)|\le\varepsilon\ \Big]\ \ge\ 1-\delta
--   $$
--
--   for every $d$-dimensional density matrix $\rho$.
--
--   The number of copies is exponentially smaller in $m$ and $d$ than for full state tomography or for estimating each $\operatorname{Tr}(E_i\rho)$ separately.
--
--   **Formalization Note** The source writes $\varepsilon,\delta\in[0,1]$; the endpoints $0$ are excluded because there $1/\varepsilon$ or $\log(1/\delta)$ is undefined. Internal randomness and post-processing of the learner are absorbed into the POVM; $\rho^{\otimes k}$ is the $k$-fold Kronecker power and logarithms are natural (the base is absorbed by the polynomial).
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 142, Theorem 6.6.2. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning



open Classical in
/-- Arunachalam p.142, Theorem 6.6.2 (Aaronson, shadow tomography): there is a polynomial `p`
such that for every `ε, δ ∈ (0, 1]`, integers `m, d > 0` and known two-outcome measurements
`{E_i, 1 − E_i}`, `i ∈ [m]`, on `ℂ^d`, some learner using `k ≤ p(log m, log d, 1/ε, log(1/δ))`
copies of the unknown state — a measurement (POVM) on `ρ^{⊗k}` whose outcomes are labelled by
numbers `b_1, …, b_m ∈ [0, 1]` — outputs, for every `d`-dimensional density matrix `ρ`, with
probability at least `1 − δ` numbers satisfying `|Tr(E_i ρ) − b_i| ≤ ε` for all `i`. The source's
`ε, δ ∈ [0, 1]` is corrected to `(0, 1]`: at `ε = 0` or `δ = 0` the bound `poly(1/ε, log(1/δ))`
is undefined. -/
theorem shadowTomography :
    ∃ p : MvPolynomial (Fin 4) ℝ, ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 →
      ∀ m d : ℕ, 0 < m → 0 < d →
        ∀ E : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ i, IsEffect (E i)) →
          ∃ k : ℕ, (k : ℝ) ≤ MvPolynomial.eval
              ![Real.log (m : ℝ), Real.log (d : ℝ), 1 / ε, Real.log (1 / δ)] p ∧
            ∃ (O : Type) (_ : Fintype O) (Mo : O → Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)
              (b : O → Fin m → ℝ), IsPOVM Mo ∧ (∀ o i, 0 ≤ b o i ∧ b o i ≤ 1) ∧
              ∀ ρ : Matrix (Fin d) (Fin d) ℂ, IsDensityMatrix ρ →
                povmEventProb Mo (piKron k ρ)
                  (fun o => ∀ i, |effectProb (E i) ρ - b o i| ≤ ε) ≥ 1 - δ := by
  sorry

end QAlgorithms.Arunachalam
