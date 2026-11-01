-- Prove2me | Theorems.Thm_StochKolmogorov_Persist_occupation_phi_continuous
-- name    : StochKolmogorov.Persist.occupation_phi_continuous
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-01T00:47:30.30045+00:00
-- url     : https://prove2.me/theorems/39b00794-9064-4473-a5b9-db68d0cd4cd9
-- title:
--   Continuity of the occupation integral of Phi from the Feller property and the moment bound (3.8)
-- statement:
--   Let $X$ solve the stochastic Kolmogorov system $dX_i=X_i f_i(X)\,dt+X_i g_i(X)\,dE_i$ from every $x\in\mathbb R^n_+$ under Assumption 1.1 (with $c$, $\gamma_b$), let $\delta_0$ satisfy (3.2), $H$ be the constant of (3.5), and let $p\in\mathbb R^{n,\circ}_+$ with $\|p\|_1\le\delta_0$. Assume moreover that $X$ stays in $\mathbb R^n_+$, the uniform moment bound (3.8) of Lemma 3.2 holds with constant $H_2>0$, and $X$ is Feller on $\mathbb R^n_+$ ($x\mapsto\mathbb E_x h(X(t))$ continuous for bounded continuous $h$). Then
--
--   $$(x,T)\longmapsto \int_0^T\mathbb E_x\,\Phi(X(t))\,dt = T\int\Phi\,d\Pi^x_T$$
--
--   is continuous on $\mathbb R^n_+\times(0,\infty)$.
--
--   Role: the continuity in $(x,T)$, up to the boundary, that the proof of Proposition 4.1 uses (via the Feller property and Lemma 4.1) to obtain (4.14) for $x$ near $\partial\mathbb R^n_+$.
--
--   **Formalization Note**: the Feller property and (3.8) are taken as hypotheses in the exact form of Lemma 3.2.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Proposition 4.1, (4.14) (Feller property, Lemma 3.2), p. 18

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Persist

open EthierKurtz

theorem occupation_phi_continuous {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀)
    (hinv : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (hfel : ∀ (t : ℝ≥0) (h : SDEState n →ᵇ ℝ),
      ContinuousOn (fun x => ∫ ω, h (X x t ω) ∂P) (orthant n)) :
    ContinuousOn (fun q : SDEState n × ℝ => q.2 * ∫ y, Phi C c p y ∂(occMean P X q.1 q.2))
      (orthant n ×ˢ Ioi 0) := by sorry

end StochKolmogorov.Persist
