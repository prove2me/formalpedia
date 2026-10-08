-- Prove2me | Theorems.Thm_WeakMFG_Existence_lemma_7_9
-- name    : WeakMFG.Existence.lemma_7_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:28.301091+00:00
-- url     : https://prove2.me/theorems/3a09cacf-74a2-4af5-81fc-3765cffe8b10
-- title:
--   Lemma 7.9 — under (E), H is continuous on Q × P(A) × ℝ^d and the maximizer sets are upper hemicontinuous on Q × ℝ^d
-- statement:
--   Assume the standing assumptions (S) and assumption (E). Then for each $(t,x)\in[0,T]\times\mathcal C$:
--
--   1. the function $\mathcal Q\times\mathcal P(A)\times\mathbb R^d\ni(\mu,q,z)\mapsto H(t,x,\mu,q,z)$ is continuous;
--   2. the set-valued function $\mathcal Q\times\mathbb R^d\ni(\mu,z)\mapsto A(t,x,\mu,z)$ is upper hemicontinuous.
--
--   Here $H$ is the maximized Hamiltonian and $A(t,x,\mu,z)$ its set of maximizers (3.2), $\mathcal Q$ carries $\tau_\psi(\mathcal C)$ and $\mathcal P(A)$ the weak topology.
--
--   This continuity is what the stability of the BSDE (7.1) in $(\mu,\nu)$ (Lemma 7.10) and the upper hemicontinuity of the optimal-control sets (Lemma 7.11) rest on.
--
--   **Formalization Note** The maximizer set is taken at every $q\in\mathcal P(A)$ (by (S.5) it does not depend on $q$), and the claim is made for every $t\ge0$.
-- source:
--   Carmona, Lacker, A probabilistic weak formulation of mean field games and applications, arXiv:1307.1152v2 (2014), Lemma 7.9, p. 25

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_WeakMFG_Existence_Model
import Definitions.Def_WeakMFG_Existence_Hyp
import Definitions.Def_WeakMFG_Existence_Reward
import Definitions.Def_WeakMFG_Existence_FixedPoint
import Definitions.Def_WeakMFG_Existence_UHC

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

namespace WeakMFG.Existence

/-- Lemma 7.9 (Carmona–Lacker, arXiv:1307.1152v2, p. 25): suppose (E). Then for each
`(t, x) ∈ [0, T] × C`, `Q × P(A) × ℝ^d ∋ (μ, q, z) ↦ H(t, x, μ, q, z)` is continuous, and
`Q × ℝ^d ∋ (μ, z) ↦ A(t, x, μ, z)` is upper hemicontinuous.
Formalization Notes: `Q` carries `τ_ψ(C)`; continuity on `Q × P(A) × ℝ^d` is `ContinuousOn` on
`Q ×ˢ univ`; the maximizer set is taken at every `q` (by (S.5) it does not depend on `q`); stated
for every `t ≥ 0`. -/
theorem lemma_7_9 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {ψ : Path d T → ℝ}
    {EA : Type*} [NormedAddCommGroup EA] [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA]
    {A : Set EA} {Ω : Type*} [MeasurableSpace Ω] (B : Base d T Ω)
    (σ : ℝ≥0 → Path d T → Matrix (Fin d) (Fin d) ℝ)
    (b : ℝ≥0 → Path d T → Ppsi ψ → EA → (Fin d → ℝ))
    (f : ℝ≥0 → Path d T → Ppsi ψ → PA A → EA → ℝ) (g : Path d T → Ppsi ψ → ℝ)
    (X : ℝ≥0 → Ω → Fin d → ℝ) (Xp : Ω → Path d T)
    (hS : Standing B A ψ σ b f g X Xp)
    (hE : CondE B A ψ b f g Xp) (t : ℝ≥0) (x : Path d T) :
    ContinuousOn (fun p : Ppsi ψ × PA A × (Fin d → ℝ) => Ham σ b f t x p.1 p.2.1 p.2.2)
      (Qset B A σ b Xp ×ˢ Set.univ) ∧
    ∀ (q : PA A) (p : Qset B A σ b Xp × (Fin d → ℝ)),
      UHCAt (fun p : Qset B A σ b Xp × (Fin d → ℝ) => Amax σ b f t x p.1.1 q p.2) p := by sorry

end WeakMFG.Existence
