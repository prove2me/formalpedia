-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_4
-- name    : QPSpinParisi.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:35.985795+00:00
-- url     : https://prove2.me/theorems/ce9bc22b-b892-4386-8eb0-943038b9c28d
-- title:
--   Lemma 3.4 — the limit $A_\xi(\beta)$ exists, and the vector Parisi formula (3.14)
-- statement:
--   For every $\beta>0$, the limit
--   $$A_\xi(\beta)=\lim_{n\to\infty}A^Y_n(\beta)$$
--   exists. If $\xi$ is a finite mixture, it satisfies
--   $$A_\xi(\beta)=\frac{\beta^2}2\xi(1)+\inf_{\pi\in\Pi}P_{\xi,\beta}(\pi),\tag{3.14}$$
--   with $P_{\xi,\beta}(\pi)$ as in (3.13). This is the finite-temperature input of the proof, imported from the vector spin glass literature.
--
--   Differences from the source:
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - encoding: infimum over $\Pi$ of (3.13) with a continuous Ruelle cascade → infimum over step paths, with the cascade written as a recursion; reason: step paths are dense and the functional is $L^1$-Lipschitz (estimates quoted on p.21; the same passage on p.18), so the infima are equal
--   - encoding: $A_\xi$ defined for $\beta>0$ → a function $A:\mathbb R\to\mathbb R$, unconstrained at $\beta\le0$; reason: only $\beta>0$ is ever read
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.4, p.16 (PDF p.16)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsFreeEnergyLimit
import Definitions.Def_QPSpinParisi_PiStep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.4, p.16, PDF p.16: for every `β > 0` the limit `A_ξ(β) = lim_n A^Y_n(β)` exists, and if `ξ` is a finite mixture,
`A_ξ(β) = (β²/2) ξ(1) + inf_{π ∈ Π} P_{ξ,β}(π)` (3.14).

**Formalization Note** The infimum runs over step paths and the functional is the recursion `PiStep`, in place of the continuous Ruelle
cascade on `Π` (see `PiStep`). -/
theorem lemma_3_4 (c : ℕ → ℝ) (hc : MixHyp c) :
    ∃ A : ℝ → ℝ, IsFreeEnergyLimit c A ∧
      ((∃ P₀ : ℕ, ∀ p, P₀ < p → c p = 0) → ∀ β : ℝ, 0 < β →
        IsGLB (range (PiStep c β)) (A β - (β ^ 2 / 2) * xiS c 1)) := by sorry

end QPSpinParisi
