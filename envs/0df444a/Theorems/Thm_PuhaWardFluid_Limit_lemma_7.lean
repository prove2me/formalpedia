-- Prove2me | Theorems.Thm_PuhaWardFluid_Limit_lemma_7
-- name    : PuhaWardFluid.Limit.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:26.528483+00:00
-- url     : https://prove2.me/theorems/befa1465-a95e-4aea-8dd2-dfa36cd7de4e
-- title:
--   Lemma 7, p. 21 — |𝒜^N_{s,j}(φ,t)| ≤ ‖φ‖_∞ (X^N_j(0) + E^N_j(t)) ∫_0^m h^s_j and the reneging analogue
-- statement:
--   Consider the $N$-th queue under an HL control policy. Almost surely the following holds for every class $j$ and $t\ge0$.
--
--   1. For $0<m<H^s_j$ and every bounded measurable $\varphi:[0,H^s_j)\times\mathbb R_+\to\mathbb R$ with $\operatorname{supp}(\varphi)\subseteq[0,m]\times\mathbb R_+$,
--   $$\big|\mathcal A^N_{s,j}(\varphi,t)\big|\le\|\varphi\|_\infty\big(X^N_j(0)+E^N_j(t)\big)\int_0^mh^s_j(x)\,dx .$$
--   2. For $0<m<H^r_j$ and every bounded measurable $\psi:[0,H^r_j)\times\mathbb R_+\to\mathbb R$ with $\operatorname{supp}(\psi)\subseteq[0,m]\times\mathbb R_+$,
--   $$\big|\mathcal A^N_{r,j}(\psi,t)\big|\le\|\psi\|_\infty\big(\langle1,\eta^N_j(0)\rangle+E^N_j(t)\big)\int_0^mh^r_j(x)\,dx .$$
--
--   Here $\mathcal A^N_{s,j}(\varphi,t)=\int_0^t\langle\varphi(\cdot,u)h^s_j,\nu^N_j(u)\rangle du$ and $\mathcal A^N_{r,j}(\psi,t)=\int_0^t\langle\psi(\cdot,u)h^r_j,\eta^N_j(u)\rangle du$ are the compensators of the departure and potential-reneging marked point processes. The bound shows that these compensators define finite Radon measures.
--
--   **Formalization Note** The test functions are taken on $\mathbb R\times\mathbb R$ and only their values on $[0,H)\times\mathbb R_+$ enter; the support condition is stated as "$\varphi=0$ on $([0,H)\times\mathbb R_+)\setminus([0,m]\times\mathbb R_+)$", equivalent to the closed-support condition since $[0,m]\times\mathbb R_+$ is closed. The statement also asserts that the integrand in $u$ is integrable, so that the compensator is a genuine integral (the paper notes after the lemma that the compensators are finite). The right-hand side is computed in $[0,\infty]$.
-- source:
--   Puha & Ward, Fluid limits for multiclass many-server queues with general reneging distributions and head-of-the-line scheduling, Math. Oper. Res., Articles in Advance (21 Dec 2021), doi:10.1287/moor.2021.1166, p. 21 (PDF 22), Lemma 7 (compensators defined on p. 18)

import Mathlib
import Definitions.Def_PuhaWardFluid_Limit_Queue

open MeasureTheory
open scoped NNReal ENNReal

namespace PuhaWardFluid.Limit

/-- **Lemma 7** (p. 21). For an HL control policy of the `N`-th queue, almost surely, for each class
`j`, `0 < m < H^s_j`, `t ≥ 0` and bounded measurable `φ` on `[0, H^s_j) × ℝ₊` with
`supp(φ) ⊆ [0, m] × ℝ₊`, the compensator `𝒜^N_{s,j}(φ, t)` is a well-defined integral and
`|𝒜^N_{s,j}(φ, t)| ≤ ‖φ‖_∞ (X^N_j(0) + E^N_j(t)) ∫_0^m h^s_j(x) dx`;
similarly for `0 < m < H^r_j` and `ψ` on `[0, H^r_j) × ℝ₊`,
`|𝒜^N_{r,j}(ψ, t)| ≤ ‖ψ‖_∞ (⟨1, η^N_j(0)⟩ + E^N_j(t)) ∫_0^m h^r_j(x) dx`. -/
theorem lemma_7 {J : ℕ} (L : ClassLaws J) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : QueueSeq J Ω) (N : ℕ+) (hQ : Q.IsHLPolicy L P N) :
    ∀ᵐ ω ∂P, ∀ j : Fin J,
      (∀ (m : ℝ) (t : ℝ≥0) (φ : ℝ → ℝ → ℝ), 0 < m → ENNReal.ofReal m < L.Hs j →
        Measurable (Function.uncurry φ) →
        (∃ C : ℝ, ∀ p ∈ markDom (L.Hs j), |φ p.1 p.2| ≤ C) →
        (∀ p ∈ markDom (L.Hs j), m < p.1 → φ p.1 p.2 = 0) →
        IntegrableOn (fun u : ℝ => pair (fun x => φ x u * (L.hs j x).toReal)
            (Q.nu L N ω u.toNNReal j)) (Set.Icc 0 t) ∧
        ENNReal.ofReal |Q.Acomp_s L N ω φ t j| ≤
          ENNReal.ofReal (supNormOn (L.Hs j) φ * ((Q.x0 N ω j : ℝ) + Q.E N ω t j)) *
            ∫⁻ x in Set.Icc (0 : ℝ) m, L.hs j x) ∧
      (∀ (m : ℝ) (t : ℝ≥0) (ψ : ℝ → ℝ → ℝ), 0 < m → ENNReal.ofReal m < L.Hr j →
        Measurable (Function.uncurry ψ) →
        (∃ C : ℝ, ∀ p ∈ markDom (L.Hr j), |ψ p.1 p.2| ≤ C) →
        (∀ p ∈ markDom (L.Hr j), m < p.1 → ψ p.1 p.2 = 0) →
        IntegrableOn (fun u : ℝ => pair (fun x => ψ x u * (L.hr j x).toReal)
            (Q.eta L N ω u.toNNReal j)) (Set.Icc 0 t) ∧
        ENNReal.ofReal |Q.Acomp_r L N ω ψ t j| ≤
          ENNReal.ofReal (supNormOn (L.Hr j) ψ * ((Q.m0 N ω j : ℝ) + Q.E N ω t j)) *
            ∫⁻ x in Set.Icc (0 : ℝ) m, L.hr j x) := by sorry

end PuhaWardFluid.Limit
