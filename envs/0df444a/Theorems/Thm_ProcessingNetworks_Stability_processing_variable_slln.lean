-- Prove2me | Theorems.Thm_ProcessingNetworks_Stability_processing_variable_slln
-- name    : ProcessingNetworks.Stability.processing_variable_slln
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T17:19:27.654634+00:00
-- url     : https://prove2.me/theorems/d49936a0-2a32-4528-828d-0e54ca8c9559
-- title:
--   Proposition 2.3 — SLLN for processing variables
-- statement:
--   Under the baseline stochastic assumptions (Assumption 2.1), for each activity $j$ the
--   processing-variable pairs $(v_j(\ell), \varphi_j(\ell))_{\ell \ge 1}$ are i.i.d.\ with finite means
--   $m_j = \mathbb{E}[v_j(1)]$ and $\Gamma_j = \mathbb{E}[\varphi_j(1)]$, so the ordinary strong law of large
--   numbers applies to each coordinate sequence.
--
--   **Proposition 2.3 (SLLN for processing variables).** For each activity $j$, with probability one,
--   $$
--   \frac{1}{n} \sum_{\ell = 1}^{n} v_j(\ell) \;\longrightarrow\; m_j
--   \qquad \text{and} \qquad
--   \frac{1}{n} \sum_{\ell = 1}^{n} \varphi_j(\ell) \;\longrightarrow\; \Gamma_j
--   \qquad \text{as } n \to \infty. \tag{2.15}
--   $$
--
--   **Formalization note.** The two convergences are joined in a single almost-sure event, following
--   the book's "with probability one" covering both limits at once; the output-vector limit is stated
--   coordinate-wise ($\forall i$) since $\varphi_j(\ell)$ is $\mathbb{Z}_+^I$-valued, matching
--   `BaselineAssumptions`'s representation of $\varphi$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 31, Proposition 2.3

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Proposition 2.3 (SLLN for processing variables), Dai & Harrison, p. 31: under the baseline
stochastic assumptions, for each activity `j`, almost surely the sample means of the first `n`
service times and output vectors converge, `(1/n) ∑_{ℓ<n} vⱼ(ℓ) → mⱼ` and
`(1/n) ∑_{ℓ<n} φⱼ(ℓ) → Γⱼ`, as `n → ∞` (`ℓ = 0, …, n-1` here stands for the book's
`ℓ = 1, …, n`). -/
theorem processing_variable_slln {Ω : Type*} [MeasureSpace Ω] {I J : ℕ} {N0 : Fin J → ℕ}
    {E : Fin I → ℝ → Ω → ℕ} {lam : Fin I → ℝ≥0}
    {v : Fin J → ℕ → Ω → ℝ} {φ : Fin J → ℕ → Ω → Fin I → ℕ}
    {m : Fin J → ℝ} {Γ : Fin J → Fin I → ℝ} {Psi : Fin J → ℕ → Ω → ℝ × (Fin I → ℕ)}
    (h : BaselineAssumptions I J N0 E lam v φ m Γ Psi) (j : Fin J) :
    ℙ {ω | Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, v j ℓ ω) / n) atTop (nhds (m j)) ∧
           ∀ i : Fin I, Tendsto (fun n : ℕ => (∑ ℓ ∈ Finset.range n, (φ j ℓ ω i : ℝ)) / n)
             atTop (nhds (Γ j i))} = 1 := by sorry

end ProcessingNetworks.Stability
