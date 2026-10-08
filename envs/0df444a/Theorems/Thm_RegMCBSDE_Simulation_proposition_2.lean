-- Prove2me | Theorems.Thm_RegMCBSDE_Simulation_proposition_2
-- name    : RegMCBSDE.Simulation.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:57.557236+00:00
-- url     : https://prove2.me/theorems/19e68f0f-cb90-4ae0-aa7e-19a874be6a83
-- title:
--   Proposition 2 — a priori bounds |Y^{N,i,I}| ≤ ρ_{0,k}, √h|Z^{N,i,I}_l| ≤ ρ_{l,k} with ρ = max(1, C₀|p|)
-- statement:
--   Let the model satisfy (H1)–(H2), let the bases $p_{l,k}$ be square integrable with invertible Gram matrices $\mathbb E[p_{l,k}p_{l,k}^*]$, and for each $I\ge0$ let $(\alpha^{i,I})_{i\ge0}$ be the projection–Picard scheme of Definition 1, with $Y^{N,i,I}_{t_k}=\alpha^{i,I}_{0,k}\cdot p_{0,k}(P^N_{t_k})$ and $Z^{N,i,I}_{l,t_k}=\alpha^{i,I}_{l,k}\cdot p_{l,k}(P^N_{t_k})$. Then, for $h=T/N$ small enough, there is a constant $C_0$ such that the functions $\rho^N_{l,k}(\cdot)=\max(1,C_0|p_{l,k}(\cdot)|)$ satisfy, almost surely,
--   $$|Y^{N,i,I}_{t_k}|\le\rho^N_{0,k}(P^N_{t_k}),\qquad \sqrt h\,|Z^{N,i,I}_{l,t_k}|\le\rho^N_{l,k}(P^N_{t_k})$$
--   for every $i\ge0$, $I\ge0$, $0\le k\le N-1$ and $1\le l\le q$.
--
--   These bounds are the a priori estimates that fix the truncation levels of the simulation-based scheme: the truncated empirical estimates are forced to satisfy the same bounds as the quantities they approximate.
--
--   **Formalization Note** The paper states the result without a smallness condition on $h$, but its proof relies on the uniform bound (19), which holds only for $h$ small; the statement is therefore formalized "for $h=T/N<h_0$", with $h_0$ depending only on the model. "For some constant $C_0$ large enough" is an existential: $C_0$ may depend on all the data (the bases, $N$, $S_0$), and is the same for all $I$ and $i$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 16, Proposition 2 (proof p. 18)

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting
import Definitions.Def_RegMCBSDE_Simulation_ProjectionScheme

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- Proposition 2, p. 16 (proof p. 18): a priori bounds for the projection–Picard iterates, which
fix the truncation levels. Under (H1)–(H2), for `h = T/N` small enough, for every choice of data
with admissible bases (square-integrable, invertible Gram matrices) and every family of
projection–Picard schemes `α^{i,I}` (one for each `I ≥ 0`), there is a constant `C₀` such that,
with `ρ^N_{l,k}(·) = max(1, C₀ |p_{l,k}(·)|)`, almost surely
`|Y^{N,i,I}_{t_k}| ≤ ρ^N_{0,k}(P^N_{t_k})` and `√h |Z^{N,i,I}_{l,t_k}| ≤ ρ^N_{l,k}(P^N_{t_k})`
for all `i ≥ 0`, `I ≥ 0`, `0 ≤ k ≤ N-1`, `1 ≤ l ≤ q`.

Pinned readings: the printed statement has no "for `h` small enough"; its proof uses (19), which
holds only for `h` small, so `T/N < h₀` is added (`h₀` depends only on the model). `C₀` may depend
on all the data ("for some constant `C₀` large enough"). (H3) is not used (no continuous-time
terminal functional appears). -/
theorem proposition_2 {d q : ℕ} (m : Model d q) (hm : m.Standing) :
    ∃ h₀ > 0, ∀ (d' : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (D : RefData d q d' Ω) (B : Basis q d'),
      m.h D.N < h₀ → D.IsAdmissible m P → B.IsAdmissible D P →
      ∀ α : ℕ → ℕ → (k : ℕ) → Coeff B k, (∀ I, IsProjectionScheme m D B P I (α I)) →
      ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ I, Prop2Bounds m D B P C0 (α I) := by sorry

end RegMCBSDE.Simulation
