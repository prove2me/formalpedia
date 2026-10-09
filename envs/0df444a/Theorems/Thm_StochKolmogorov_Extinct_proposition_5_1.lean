-- Prove2me | Theorems.Thm_StochKolmogorov_Extinct_proposition_5_1
-- name    : StochKolmogorov.Extinct.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:33:15.048822+00:00
-- url     : https://prove2.me/theorems/754af0f2-b2a3-4a11-89f4-51d62f3610d4
-- title:
--   Proposition 5.1 — local contraction of Uθ
-- statement:
--   Under Assumption 1.3 and with $M,T_e,\delta_e,n_e,\widehat p,\check p,\rho_e$ as in Lemma 5.2, some $\theta\in(0,\delta_0)$ satisfies, for every $T\in[T_e,n_eT_e]$ and strictly positive $x$ with $\|x\|_1\le M$ and each missing coordinate below $\delta_e$,
--
--   $$\mathbb E_x U_\theta(X(T))\le\exp(-\tfrac12\theta\rho_e T)U_\theta(x).$$
--
--   This is the contraction estimate near the selected boundary face.
--
--   **Formalization Note** The preceding Lemma 5.2 inequality is represented as a hypothesis identifying the chosen $T_e,\delta_e$; the existential $\theta$ is chosen before $T$ and $x$.
--
--   **Moderation note** The chosen constants carry the integrability and drift bound of Lemma 5.2; the expected $U_\theta$ is integrable.
-- source:
--   Hening, Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, Proposition 5.1, pp. 21–22

import Mathlib
import Definitions.Def_StochKolmogorov_Extinct_Extinction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Extinct

open EthierKurtz

theorem proposition_5_1 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
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
    (ne : ℕ) (hne : Hconst C c γb δ₀ < γb * ((ne : ℝ) - 1))
    (Te δe : ℝ) (hTe : 0 < Te) (hδe : 0 < δe)
    (h53 : ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
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
            pcheck * lyapAvg P C X i T x ≤ -ρe) :
    ∃ θ : ℝ, 0 < θ ∧ θ < δ₀ ∧
      ∀ T : ℝ, T ∈ Set.Icc Te ((ne : ℝ) * Te) →
        ∀ x ∈ openOrthant n, l1 x ≤ M →
          (∀ i : Fin n, i ∉ supp mu → x i < δe) →
          Integrable (fun ω => Utheta c mu phat pcheck θ (X x T.toNNReal ω)) P ∧
          ∫ ω, Utheta c mu phat pcheck θ (X x T.toNNReal ω) ∂P ≤
            Real.exp (-(1 / 2) * θ * ρe * T) * Utheta c mu phat pcheck θ x := by sorry

end StochKolmogorov.Extinct
