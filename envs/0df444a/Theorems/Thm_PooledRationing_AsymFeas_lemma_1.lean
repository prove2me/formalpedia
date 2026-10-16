-- Prove2me | Theorems.Thm_PooledRationing_AsymFeas_lemma_1
-- name    : PooledRationing.AsymFeas.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:33.942017+00:00
-- url     : https://prove2.me/theorems/34a0a9bb-5ec6-4bc7-a465-2833ce9ed9f2
-- title:
--   Lemma 1 — pointwise minimization yields the least expected dual value
-- statement:
--   Fix nonnegative weights $w$ and a deterministic policy $\phi_w$ that minimizes the Max-Weighted-Service objective $f(y)-\sum_jw_jR_j(s_j,D_j)$ over $P(c,D)$ for every demand realization $D$. Then
--   $$
--   \inf_{\phi}F(w,\phi)=F(w,\phi_w)=\mathbb E_F[g(w,c;D)],
--   $$
--   where $F(w,\phi)$ is expected allocation cost minus weighted expected service, and $g(w,c;D)$ is the corresponding pointwise minimum. This identifies a policy that attains the dual infimum.
--
--   **Formalization Note** The policy is measurable and feasible at every $D$. Service measures are nonnegative and jointly measurable on the real extension of their original domain. One integrable envelope bounds service and absolute allocation cost on every feasible set, ensuring all expectations are genuine Bochner integrals. Randomized policies are finite mixtures when they occur elsewhere in this development.
-- source:
--   Jiang, Wang & Zhang, Achieving High Individual Service-Levels without Safety Stock? Optimal Rationing Policy of Pooled Resources, SSRN 3385089 (version of 31 July 2021), p. 12, Lemma 1, (17); proof p. 41

import Mathlib
import Definitions.Def_PooledRationing_AsymFeas_Setting

namespace PooledRationing.AsymFeas

open MeasureTheory

/-- Jiang–Wang–Zhang, Lemma 1, equation (17), p. 12. -/
theorem lemma_1 {n m : ℕ} (F : Measure (Fin n → ℝ)) [IsProbabilityMeasure F]
    (P : (Fin m → ℝ) → (Fin n → ℝ) → Set (Sol n m)) (c : Fin m → ℝ)
    (f : (Fin m → Fin n → ℝ) →ₗ[ℝ] ℝ)
    (R : Fin n → ℝ → ℝ → ℝ) (β : Fin n → ℝ)
    (hRnonneg : ∀ j s d, 0 ≤ R j s d)
    (hRmeas : ∀ j, Measurable (fun p : ℝ × ℝ => R j p.1 p.2))
    (h : (Fin n → ℝ) → ℝ) (hh : Integrable h F)
    (hRenv : ∀ D, ∀ x ∈ P c D, ∀ j, R j (x.1 j) (D j) ≤ h D)
    (hfenv : ∀ D, ∀ x ∈ P c D, |f x.2| ≤ h D)
    (w : Fin n → ℝ) (hw : 0 ≤ w)
    (φw : DetPolicy P c)
    (hφw : ∀ D, IsMinOn (mwsObjective f R w D) (P c D) (φw.toFun D)) :
    (⨅ φ : DetPolicy P c, Fdual F f R w φ) = Fdual F f R w φw ∧
      Fdual F f R w φw = ∫ D, g P c f R w D ∂F := by sorry

end PooledRationing.AsymFeas
