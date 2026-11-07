-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_5
-- name    : QPSpinParisi.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:21.905563+00:00
-- url     : https://prove2.me/theorems/6011fac9-1f1d-40ff-a4e9-c5ed5213d0e5
-- title:
--   Lemma 3.5 — the scalar Parisi formula (3.17), with a unique minimizer
-- statement:
--   For every $\beta>0$,
--   $$\frac{A_\xi(\beta)}\beta=\inf_{\alpha\in\mathcal M}P_{\xi,\beta}(\alpha).\tag{3.17}$$
--   The infimum is attained, and the minimizer is unique; it is denoted $\alpha_{\xi,\beta}$. The statement holds for every mixture, finite or infinite. It replaces the matrix-valued variational problem of Lemma 3.4 by a problem over a scalar order parameter.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - reading: $\Psi_{\xi,\beta,\alpha}$ as "the solution" of (3.16) → the control formula (3.23); reason: p.17 fixes no solution concept for a discontinuous coefficient, and p.19 gives (3.23) as its formula
--   - reading: "the minimizer ... is unique" → existence of a minimizer is stated too; reason: "we denote it by $\alpha_{\xi,\beta}$" presupposes it, and it is the stronger reading
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.5, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsFreeEnergyLimit
import Definitions.Def_QPSpinParisi_IsMinB

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.5, p.17, PDF p.17: for every `β > 0`, `A_ξ(β)/β = inf_{α ∈ M} P_{ξ,β}(α)` (3.17), the infimum is attained, and the
minimizer is unique. It holds for every mixture, finite or not. -/
theorem lemma_3_5 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (A : ℝ → ℝ)
    (hA : IsFreeEnergyLimit c A) (β : ℝ) (hβ : 0 < β) :
    ∃ α ∈ MSet, PfB W β α = A β / β ∧ IsMinB W β α ∧
      ∀ α' ∈ MSet, PfB W β α' = PfB W β α → α' = α := by sorry

end QPSpinParisi
