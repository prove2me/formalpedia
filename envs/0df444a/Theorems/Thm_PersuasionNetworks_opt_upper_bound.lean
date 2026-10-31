-- Prove2me | Theorems.Thm_PersuasionNetworks_opt_upper_bound
-- name    : PersuasionNetworks.opt_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:53.961252+00:00
-- url     : https://prove2.me/theorems/b9dbc6cb-e41a-4e49-9ec4-af1fe3fdb801
-- title:
--   §3.1 — the optimal value of (OPT) bounds the payoff of every mechanism
-- statement:
--   Let $(p,z)$ be an optimal solution of (OPT). For every mechanism, over every signal space,
--   $$
--   \mathbb E\bigl[\nu(\mathbb E[T\mid S])\bigr]\le\sum_{k}p_kr_k .
--   $$
--
--   So (OPT) is a relaxation of the designer's problem. It combines Lemma 1 and Lemma 2.
--
--   Differences from the source:
--   - encoding: the optimal objective value of (OPT) → the objective value at any optimal solution; reason: the same number; Lemma 3 gives that a solution exists
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, §3.1, p.17 (unnumbered)

import Mathlib
import Definitions.Def_PersuasionNetworks_Quantile
import Definitions.Def_PersuasionNetworks_Mechanism
import Definitions.Def_PersuasionNetworks_OPT

open MeasureTheory ProbabilityTheory

namespace PersuasionNetworks

/-- **(OPT) is a relaxation**, Candogan, SSRN 3346144 (preprint), §3.1, p.17 (unnumbered): "the optimal objective value of
(OPT) is an upper bound on the designer's payoff". For every mechanism `κ`, over every signal space,
the designer's payoff is at most the objective value of any optimal solution of (OPT). -/
theorem opt_upper_bound (μ : Measure ℝ) [IsProbabilityMeasure μ] (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ)
    (hμ : IsState μ 𝒯) (hstep : IsStepPayoff 𝒯 K b r)
    {p z : ℕ → ℝ} (hopt : IsOptimal μ 𝒯 K b r p z)
    {S : Type*} [MeasurableSpace S] (κ : Kernel ℝ S) [IsMarkovKernel κ] :
    designerPayoff μ (nu K b r) κ ≤ objective K r p := by sorry

end PersuasionNetworks
