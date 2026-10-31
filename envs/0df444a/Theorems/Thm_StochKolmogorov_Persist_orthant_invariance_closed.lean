-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
-- name    : StochKolmogorov.Persist.orthant_invariance_closed
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:08:58.619587+00:00
-- url     : https://prove2.me/theorems/950d4a16-ce82-411f-8b81-a3af596540e2
-- title:
--   A stochastic Kolmogorov system started in the closed orthant stays in it
-- statement:
--   Let $Y$ be a strong solution of the stochastic Kolmogorov system (1.1), $dY_i=Y_i f_i(Y)\,dt+Y_i g_i(Y)\,dE_i(t)$, driven by a standard Brownian motion, with $f_i,g_i$ locally Lipschitz on $\mathbb R^n_+$ and $Y_0=x_0\in\mathbb R^n_+$. Then for every $t\ge0$,
--
--   $$Y_t\in\mathbb R^n_+ \quad\text{a.s.}$$
--
--   Role: invariance of the closed orthant (the face case $I=\{1,\dots,n\}$ closure of Lemma 3.1), used for the Markov property of the solution on $\mathbb R^n_+$.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, https://arxiv.org/abs/1704.06984, Lemma 3.1 (p. 14, invariance of the faces)

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_IsStandardBrownian
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Persist

open EthierKurtz

theorem orthant_invariance_closed {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ orthant n := by sorry

end StochKolmogorov.Persist
