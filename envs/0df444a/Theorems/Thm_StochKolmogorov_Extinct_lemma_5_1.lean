-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_lemma_5_1
-- name    : StochKolmogorov.Extinct.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:44.448355+00:00
-- url     : https://prove2.me/theorems/0da2a8f0-805c-4fe1-a6a8-8f4f853c5391
-- title:
--   Lemma 5.1 — surviving species have zero invasion rate
-- statement:
--   Let $\mu$ be any boundary ergodic invariant probability law and let $I_\mu$ be the species present on its face. Then every species present on that face has zero invasion rate:
--
--   $$\lambda_i(\mu)=0\qquad(i\in I_\mu).$$
--
--   This separates the growth rates of resident species from the negative rates required of missing species by Assumption 1.3.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.1, pp. 20–21

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem lemma_5_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
     :
    ∀ mu ∈ bdryErgodic P X, ∀ i ∈ supp mu, lyap C i mu = 0 := by sorry

end StochKolmogorov.Extinct
