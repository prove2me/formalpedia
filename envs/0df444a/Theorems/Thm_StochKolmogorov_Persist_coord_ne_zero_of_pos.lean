-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_coord_ne_zero_of_pos
-- name    : StochKolmogorov.Persist.coord_ne_zero_of_pos
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-30T18:09:13.567773+00:00
-- url     : https://prove2.me/theorems/161c99c0-e623-4ac2-9ad4-42736ddcb574
-- title:
--   A positive coordinate of a stochastic Kolmogorov system never reaches zero
-- statement:
--   Let $Y$ be a strong solution of the stochastic Kolmogorov system (1.1), $dY_i=Y_i f_i(Y)\,dt+Y_i g_i(Y)\,dE_i(t)$, driven by a standard Brownian motion, with $f_i,g_i$ locally Lipschitz on $\mathbb R^n_+$, started at $x_0$ with $x_{0,k}>0$. Then for every $t\ge0$,
--
--   $$Y_t^{(k)}\neq 0 \quad\text{a.s.}$$
--
--   Role: the interior part of the invariance of the faces in Lemma 3.1 (a species present initially is never extinct in finite time), used for the invariance of $\mathbb R^{n,\circ}_+$.
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

theorem coord_ne_zero_of_pos {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (k : Fin n) (hk : 0 < x₀ k) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω k ≠ 0 := by sorry

end StochKolmogorov.Persist
