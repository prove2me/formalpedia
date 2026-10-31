-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_pathwise_unique
-- name    : StochKolmogorov.Persist.kolmogorov_sde_pathwise_unique
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:50:56.028059+00:00
-- url     : https://prove2.me/theorems/bfbef451-df79-4ea1-a2ef-afecd7090a44
-- title:
--   Pathwise uniqueness for the stochastic Kolmogorov system under locally Lipschitz rates
-- statement:
--   If every $f_i$ and $g_i$ is locally Lipschitz on $\mathbb R^n_+$, then any two solutions of the stochastic Kolmogorov system from the same $x\in\mathbb R^n_+$ on the same Brownian motion are indistinguishable:
--
--   $$\mathbb P\big(Y_t=Y'_t\ \text{for all } t\ge0\big)=1.$$
--
--   Role: clause 2 of Lemma 3.1 (pathwise uniqueness).
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.1 (2), p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem kolmogorov_sde_pathwise_unique {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ x ∈ orthant n, ∀ Y Y' : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y' →
      ∀ᵐ ω ∂P, ∀ t, Y t ω = Y' t ω := by sorry

end StochKolmogorov.Persist
