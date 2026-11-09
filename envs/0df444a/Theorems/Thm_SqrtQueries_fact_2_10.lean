-- Prove2me | Theorems.Thm_SqrtQueries_fact_2_10
-- name    : SqrtQueries.fact_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:28:58.86018+00:00
-- url     : https://prove2.me/theorems/bcbc84ef-ecc1-4c95-b9f2-ecdb1b1c3806
-- title:
--   Fact 2.10 — $|\mathbf{Pr}_\rho[E]-\mathbf{Pr}_\sigma[E]|\le D(\rho,\sigma)$
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices on $\mathbb C^n$, let $\{M_x\}_{x=0}^{m-1}$ be a POVM (positive semidefinite matrices with $\sum_xM_x=I$) and let $E\subseteq\{0,\dots,m-1\}$ be an event. Write $\mathbf{Pr}_\rho[E]$ $=\sum_{x\in E}\operatorname{Tr}(\rho M_x)$ for the probability of $E$ when the POVM is applied to $\rho$, and similarly for $\sigma$. Then
--   $$
--   \big|\mathbf{Pr}_\rho[E]-\mathbf{Pr}_\sigma[E]\big|\le D(\rho,\sigma),\qquad D(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1 .
--   $$
--
--   This converts a trace-distance bound on the final states of an algorithm into a bound on its output probabilities.
--
--   **Formalization Note** The POVM has outcomes $\{0,\dots,m-1\}$ (`WildeQIT.Packing.IsPOVM`), and $\mathbf{Pr}_\rho[E]=\sum_{x\in E}\operatorname{Tr}(\rho M_x)$ is written with the published outcome probability `FuchsVdGraaf.outcomeDist`. The published `WildeQIT.traceDist` is $\|\rho-\sigma\|_1$ without the factor $\tfrac12$, so the right-hand side is `(1/2) * traceDist ρ σ`.
--
--   Differences from the source:
--   - encoding: any POVM → a POVM with finitely many outcomes Fin m; reason: for an event E of any POVM, the two-outcome POVM {M(E), I − M(E)} gives the same probability
-- source:
--   Ma–Tang, Square-root queries can help, STOC 2027 submission (manuscript sha256 783868e7…c5f15a), Fact 2.10, p.13

import Mathlib
import Definitions.Def_WildeQIT_Packing_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceDist

namespace SqrtQueries

/-- **Fact 2.10** of Ma–Tang, *Square-root queries can help*, STOC 2027 submission manuscript
(sha256 783868e7…c5f15a), p.13: for density matrices `ρ`, `σ`, every POVM `{M_x}` and every event
`E` (a set of outcomes), `|Pr_ρ[E] − Pr_σ[E]| ≤ D(ρ, σ)`, where `D(ρ, σ) = ½‖ρ − σ‖₁` is the trace
distance and `Pr_ρ[E] = ∑_{x ∈ E} Tr(ρ M_x)`.

**Formalization Note.** The POVM has the outcomes `Fin m` (`WildeQIT.Packing.IsPOVM`: positive
semidefinite elements summing to `I`), and the outcome probability `Tr(ρ M_x)` is the published
`FuchsVdGraaf.outcomeDist ρ M x`. The paper's trace distance `D(ρ, σ) = ½‖ρ − σ‖₁` (p.13) is
`(1/2) * WildeQIT.traceDist ρ σ`: the published `traceDist` is `‖ρ − σ‖₁` without the factor `½`.
Density matrices are `WildeQIT.IsDensityOperator` (positive semidefinite, trace one). -/
theorem fact_2_10 {n : Type} [Fintype n] [DecidableEq n] {m : ℕ} (M : Fin m → Matrix n n ℂ)
    (hM : WildeQIT.Packing.IsPOVM M) (ρ σ : Matrix n n ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (hσ : WildeQIT.IsDensityOperator σ) (E : Finset (Fin m)) :
    |∑ x ∈ E, FuchsVdGraaf.outcomeDist ρ M x - ∑ x ∈ E, FuchsVdGraaf.outcomeDist σ M x| ≤
      (1 / 2) * WildeQIT.traceDist ρ σ := by sorry

end SqrtQueries
