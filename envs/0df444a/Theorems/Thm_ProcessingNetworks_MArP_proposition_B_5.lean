-- Prove2me | Theorems.Thm_ProcessingNetworks_MArP_proposition_B_5
-- name    : ProcessingNetworks.MArP.proposition_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:21.002512+00:00
-- url     : https://prove2.me/theorems/c34a0f3d-462e-4bfe-bd78-7b67c8999050
-- title:
--   Proposition B.5 — the scaled Poisson process is uniformly integrable
-- statement:
--   Let $E=\{E(t),t\ge 0\}$ be a Poisson process with rate $\lambda>0$, and fix $h>0$. The family of random variables
--   $$
--   \Big\{\frac1tE(th),\ t\ge 1\Big\}
--   $$
--   is uniformly integrable.
--
--   This is the elementary bound behind the uniform integrability of a Markovian arrival process, whose arrival counts are dominated by Poisson counts.
--
--   Differences from the source:
--   - encoding: a Poisson process $E$ with rate $\lambda>0$ → the published `IsPoissonProcess ℙ lam E`, with `lam : ℝ≥0` and paths $\Omega\to\mathbb R\to\mathbb R$; reason: the book does not define a Poisson process and this is the standard definition.
--   - encoding: the family indexed by real $t\ge 1$ → index type `Set.Ici 1`; reason: the same index set, written as a subtype.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Proposition B.5, p.266 (PDF p.282)

import Mathlib
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
import Definitions.Def_ProcessingNetworks_MArP_IsUniformlyIntegrable

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProcessingNetworks.MArP

/-- Proposition B.5 (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, p.266,
PDF p.282). Let `E = {E(t), t ≥ 0}` be a Poisson process with rate `λ > 0` and fix `h > 0`. The family
of random variables `{(1/t) E(th), t ≥ 1}` is uniformly integrable.

**Formalization Note.** The family is indexed by the real numbers `t ≥ 1`, as the subtype
`Set.Ici 1`. A Poisson process is the published
`RankBasedSDI.LoadBalancing.IsPoissonProcess`, whose paths are real-valued. -/
theorem proposition_B_5 {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (lam : ℝ≥0) (hlam : 0 < lam) (E : Ω → ℝ → ℝ)
    (hE : RankBasedSDI.LoadBalancing.IsPoissonProcess ℙ lam E) (h : ℝ) (hh : 0 < h) :
    IsUniformlyIntegrable
      (fun (t : Set.Ici (1 : ℝ)) ω => (1 / (t : ℝ)) * E ω ((t : ℝ) * h)) := by sorry

end ProcessingNetworks.MArP
