-- Prove2me | Theorems.Thm_TransvectionMixing_lemma_2_1_extension_of_uniform_bounds
-- name    : TransvectionMixing.lemma_2_1_extension_of_uniform_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:30.858924+00:00
-- url     : https://prove2.me/theorems/3caddaf4-40fb-417b-842e-1a738b50a2a3
-- title:
--   Lemma 2.1 — extension of uniform bounds
-- statement:
--   Let $P$ be a Markov kernel (a stochastic matrix) on a finite state space $\mathcal X$ with stationary distribution $\pi$.
--
--   1. Let $R$ be auxiliary randomness independent of the chain, and $\Phi(X,R)\ge 0$. Then
--   $$
--   t\ \longmapsto\ \sup_{x\in\mathcal X}\mathbb E_x\bigl[\Phi(X_t,R)\bigr]
--   $$
--   is nonincreasing in $t$.
--   2. The quantity $\sup_{x\in\mathcal X}\|P^t(x,\cdot)-\pi\|_{TV}$ is nonincreasing in $t$.
--
--   This is how bounds proved at a scheduled length extend to every later time.
--
--   **Formalization Note** $R$ has law $\mu$ on an arbitrary probability space and $\Phi$ takes values in $[0,\infty]$; by independence $\mathbb E_x[\Phi(X_t,R)]=\sum_y P^t(x,y)\int\Phi(y,r)\,d\mu(r)$. Part 2 uses the published `MarkovMixing.distStationary`.
--
--   Differences from the source:
--   - generalization: Φ(X, R) ≥ 0 real-valued, R auxiliary randomness → Φ with values in [0, ∞] and R on an arbitrary probability space (Ω, μ); reason: every real Φ ≥ 0 and every R are instances, and the expectation is always defined
--   - encoding: 𝔼_x[Φ(X_t, R)] with R independent of the chain → ∑_y P^t(x, y) ∫⁻ Φ(y, r) dμ(r); reason: independence; same values
--   - encoding: sup_x ‖P^t(x, ·) − π‖_TV → `MarkovMixing.distStationary P π t`; reason: published definition of the same quantity
-- source:
--   Braverman, Jain, Newman, Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over Large Fields (manuscript, sha256 217f833f…), Lemma 2.1, p.8

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing

namespace TransvectionMixing

open scoped ENNReal

/-- **Lemma 2.1** (extension of uniform bounds) (Braverman–Jain–Newman, *Optimal Marginal Mixing for Transvection-Based Trapdoored Matrices over
Large Fields*, manuscript sha256 217f833f…, §2, p.8). Let `P` be a Markov kernel on a
finite state space with stationary distribution `π`.
(i) For auxiliary randomness `R` (law `μ`) independent of the chain and `Φ(X, R) ≥ 0`,
`sup_x 𝔼_x[Φ(X_t, R)]` is nonincreasing in `t`.
(ii) `sup_x ‖P^t(x, ·) − π‖_TV` is nonincreasing in `t`.

**Formalization Note** `R` lives on an arbitrary probability space `(Ω, μ)` and `Φ` takes
values in `[0, ∞]`, so no integrability condition is needed; by independence
`𝔼_x[Φ(X_t, R)] = ∑_y P^t(x, y) ∫ Φ(y, r) dμ(r)`. Part (ii) uses the published
`MarkovMixing.distStationary` (`max_x ‖P^t(x,·) − π‖_TV`). -/
theorem lemma_2_1_extension_of_uniform_bounds {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P) (π : V → ℝ)
    (hπ : MarkovMixing.IsStationary P π) :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (Φ : V → Ω → ℝ≥0∞),
        Antitone (fun t : ℕ => ⨆ x : V,
          ∑ y : V, ENNReal.ofReal ((P ^ t) x y) * ∫⁻ r, Φ y r ∂μ)) ∧
      Antitone (fun t : ℕ => MarkovMixing.distStationary P π t) := by sorry

end TransvectionMixing
