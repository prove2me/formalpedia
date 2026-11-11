-- Prove2me | Theorems.Thm_QVolKLS_lemma_3_4
-- name    : QVolKLS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:55.061242+00:00
-- url     : https://prove2.me/theorems/fdee929d-bbe1-448f-bc3e-71c9bd6cc969
-- title:
--   Lemma 3.4 — growth of the fourth-moment norm: $\||\Psi\rangle_{SA}\|_{4,\pi_u}\le B(1+2q)$
-- statement:
--   Let $\{\pi_v:v\in I\}$ be one law or a pair of mutually absolutely continuous laws on a finite sample space with
--   $$
--   \int\Big(\frac{d\pi_v}{d\pi_u}\Big)^2d\pi_u\le B^4\qquad(u,v\in I),
--   $$
--   $B\ge0$. Start a circuit from $|\pi_r\rangle_S\otimes|w\rangle_A$, where $r\in I$ and $|w\rangle_A$ is a unit vector. Suppose each gate is sample-controlled, a selective phase through some $|\pi_v\rangle_S$, or a controlled qsample reflection $R_{\pi_v}$, each possibly controlled by an auxiliary projector; the sample register is never exchanged with another one. After $q$ selective phases and controlled reflections, the state satisfies
--   $$
--   \||\Psi\rangle_{SA}\|_{4,\pi_u}\le B(1+2q)\qquad(u\in I).
--   $$
--
--   This bounds the fourth-moment norm of every reference input to a reflection in the volume algorithm, which is what Theorem 3.3's error bound needs.
--
--   **Formalization Note** On a finite sample space mutual absolute continuity means a common support, taken as the sample space, so the laws are positive.
--
--   Differences from the source:
--   - encoding: one law or a pair of mutually absolutely continuous laws → k ∈ {1, 2} laws, all positive on the finite sample space Ω; reason: Ω is the common support; every operation keeps the state supported on it
--   - reading: the bound B in ∫(dπ_v/dπ_u)² dπ_u ≤ B⁴ → B ≥ 0; reason: the hypothesis constrains only B⁴; the conclusion is meant for the nonnegative root
--   - generalization: after q selective phases; the same bound when the counted operations are controlled qsample reflections → lists mixing selective phases and controlled reflections, q counting both; reason: each kind raises the norm by at most 2B; specializes to either kind alone
--   - encoding: auxiliary register A → any complex inner product space H; reason: covers every auxiliary register
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Lemma 3.4, p.27 (operations from its proof, pp.27–28)

import Definitions.Def_QVolKLS_SampleOp

set_option autoImplicit false

namespace QVolKLS

open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Lemma 3.4 (Growth of the
fourth-moment norm)**, p.27. Let `{π_v : v ∈ I}` be one law or a pair of mutually absolutely
continuous laws with `∫ (dπ_v/dπ_u)² dπ_u ≤ B⁴` for all `u, v ∈ I`. Start from `|π_r⟩_S ⊗ |w⟩_A`
(`r ∈ I`) and apply sample-controlled gates, selective phases through `|π_v⟩_S` and controlled qsample
reflections, each possibly controlled by an auxiliary projector. After `q` selective phases and
controlled reflections, `‖|Ψ⟩_SA‖_{4,π_u} ≤ B(1 + 2q)` for every `u ∈ I`.

**Formalization Note.**
* `I = Fin k` with `k ∈ {1, 2}`. On a finite sample space mutual absolute continuity means a common
  support; the sample space `Ω` is taken to be that support, so every `π_v` is positive on `Ω` (every
  operation keeps the state supported there). `∫ (dπ_v/dπ_u)² dπ_u = Σ_x π_v(x)²/π_u(x)`.
* `B ≥ 0` (the hypothesis constrains only `B⁴`). `w` is a unit vector of the auxiliary space `H`.
* The circuit is any list of the three operations (`SampleOp`); the sample register is never exchanged
  with another one because no such operation exists in the list. The list may mix selective phases
  and controlled reflections; `q = countedOps ops` counts both. -/
theorem lemma_3_4 {Ω : Type*} [Fintype Ω] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (k : ℕ) (hk : k = 1 ∨ k = 2) (πs : Fin k → Ω → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hpos : ∀ v x, 0 < πs v x) (hsum : ∀ v, ∑ x, πs v x = 1)
    (hmom : ∀ u v, ∑ x, πs v x ^ 2 / πs u x ≤ B ^ 4)
    (r : Fin k) (w : H) (hw : ‖w‖ = 1) (ops : List (SampleOp Ω k H)) :
    ∀ u : Fin k,
      fourthMomentNorm (πs u) (runOps πs ops (fun x => ((Real.sqrt (πs r x) : ℝ) : ℂ) • w)) ≤
        ENNReal.ofReal (B * (1 + 2 * (countedOps ops : ℝ))) := by sorry

end QVolKLS
