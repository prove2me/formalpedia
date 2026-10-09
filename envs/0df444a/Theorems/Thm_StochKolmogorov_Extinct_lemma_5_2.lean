-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_lemma_5_2
-- name    : StochKolmogorov.Extinct.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:06.218133+00:00
-- url     : https://prove2.me/theorems/b78ad19e-1a49-4bd5-bf95-4b1133c44e27
-- title:
--   Lemma 5.2 — negative averaged logarithmic drift
-- statement:
--   Take $M$ from (3.1), $H$ from (3.5), and weights and margin $\widehat p,\check p,\rho_e$ satisfying (5.2). If $\gamma_b(n_e-1)>H$, there are $T_e>0$ and $\delta_e>0$ such that for $T\in[T_e,n_eT_e]$ and any orthant state $x$ with $\|x\|_1\le M$ and $x_i<\delta_e$ for missing species,
--
--   $$\overline C_T(x)-\sum_{j\in I_\mu}\widehat p_j\,\overline\lambda_{j,T}(x)+\check p\max_{i\notin I_\mu}\overline\lambda_{i,T}(x)\le-\rho_e.$$
--
--   Here the bars are the expected time averages of the $c$ bracket and instantaneous invasion rates displayed in (5.3).
--
--   **Formalization Note** The printed $T_e\ge0$ is strengthened to $T_e>0$, as the proof states, because (5.3) divides by $T$. The maximum upper bound is expressed pointwise for every missing index.
--
--   **Moderation note** The conclusion also states integrability of both time-space averages in (5.3), ruling out default real-integral values.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Lemma 5.2, p. 21

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem lemma_5_2 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (mu : Measure (SDEState n)) (h13 : Assumption13 P C X mu)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀)
    (phat : Fin n → ℝ) (hphat : (∀ i ∈ supp mu, 0 < phat i ∧ phat i < δ₀) ∧
      (∑ i ∈ supp mu, phat i) ≤ δ₀)
    (pcheck : ℝ) (hpcheck : 0 < pcheck ∧ pcheck < δ₀)
    (ρe : ℝ) (hρe : 0 < ρe)
    (h52 : ∀ ν : Measure (SDEState n), (ν ∈ subErgodic P X mu ∨ ν = mu) →
      ∀ i : Fin n, i ∉ supp mu →
        3 * ρe < (∑ j ∈ supp mu, phat j * lyap C j ν) - pcheck * lyap C i ν)
    (ne : ℕ) (hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1)) :
    ∃ Te : ℝ, 0 < Te ∧ ∃ δe : ℝ, 0 < δe ∧
      ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
        ∀ x ∈ orthant n, l1 x ≤ M →
          (∀ i : Fin n, i ∉ supp mu → x i < δe) →
          Integrable (fun q : ℝ × Ω =>
            cBracket C c (X x q.1.toNNReal q.2))
            ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) ∧
          (∀ j : Fin n, Integrable (fun q : ℝ × Ω =>
            C.f j (X x q.1.toNNReal q.2) -
              C.sig j j * C.g j (X x q.1.toNNReal q.2) ^ 2 / 2)
            ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P)) ∧
          ∀ i : Fin n, i ∉ supp mu →
            cAvg P C X c T x - (∑ j ∈ supp mu, phat j * lyapAvg P C X j T x) +
              pcheck * lyapAvg P C X i T x ≤ -ρe := by sorry

end StochKolmogorov.Extinct
