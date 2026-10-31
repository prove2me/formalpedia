-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_exists
-- name    : StochKolmogorov.Persist.kolmogorov_sde_exists
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-31T03:51:16.978089+00:00
-- url     : https://prove2.me/theorems/e99604a6-f5a1-40aa-a41c-b42cd4370800
-- title:
--   Strong existence for the stochastic Kolmogorov system from every point of the closed orthant
-- statement:
--   Under Assumption 1.1, for every $x\in\mathbb R^n_+$ the stochastic Kolmogorov system $dX_i=X_if_i(X)\,dt+X_ig_i(X)\,dE_i$ driven by the given Brownian motion $B$ has a strong solution with $X(0)=x$:
--
--   $$\exists\,Y:\quad Y_t=x+\int_0^t\operatorname{diag}(Y)\,g(Y)\,dE+\int_0^t\operatorname{diag}(Y)f(Y)\,du.$$
--
--   Role: clause 1 of Lemma 3.1 (existence), proved by truncation, Picard iteration, localization and the non-explosion estimate from the Lyapunov function $1+c^\top x$.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, Lemma 3.1 (1), p. 14

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem kolmogorov_sde_exists {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (hB : IsStandardBrownian P B) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    {x : SDEState n} (hx : x ∈ orthant n) :
    ∃ Y : ℝ≥0 → Ω → SDEState n, SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y := by sorry

end StochKolmogorov.Persist
