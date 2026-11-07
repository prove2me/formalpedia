-- Prove2me | Theorems.Thm_PathRecording_claim_5_6
-- name    : PathRecording.claim_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T08:09:36.049772+00:00
-- url     : https://prove2.me/theorems/ab01677d-62e6-4d5b-ba7e-84988c063f1a
-- title:
--   Claim 5.6 — $Q_\rho(|x\rangle\otimes\Theta_t)=\sum_y|y\rangle\otimes\Theta_{t+1}\mathrm{App}^{(t)}_{x,y}$
-- statement:
--   Let $G$ be a compact group with Haar probability measure and $\rho:G\to U(N)$ a continuous unitary representation. For every $x\in B(V)$ and every path basis vector $|\vec x,\vec y\rangle\in\mathrm{Path}_t$,
--   $$Q_\rho\big(|x\rangle\otimes\Theta_t|\vec x,\vec y\rangle\big)=\sum_{y\in B(V)}|y\rangle\otimes\Theta_{t+1}\,\mathrm{App}^{(t)}_{x,y}|\vec x,\vec y\rangle.\qquad(5.19)$$
--
--   One query to the uncompressed oracle appends the input–output pair $(x,y)$ to the matrix-element function, in superposition over the output $y$.
--
--   Differences from the source:
--   - generalization: G a compact Lie group with its normalized Haar measure dg → G any compact topological group with a Borel σ-algebra and a left Haar probability measure μ; reason: the Lie structure is never used; a compact Lie group is such a group, and on it (second countable) every left Haar probability measure is the normalized, regular, bi-invariant Haar measure of Definition 3.1; on a general compact group Lean also admits left Haar measures that are not regular, which only enlarges the statement
--   - encoding: V ⊗ L²(G) with Q_ρ(|x⟩⊗|f⟩) = ∫ f(g) ρ(g)|x⟩⊗|g⟩ dg → Fin N → Lp ℂ 2 μ, with (Q_ρ φ)_y = Σ_x ⟨y|ρ(·)|x⟩ · φ_x (multiplication by the continuous matrix entries as L^∞ functions); reason: (4.1) extended linearly; V ⊗ L²(G) ≅ L²(G)^N
--   - encoding: the operator identity Q_ρ·(|x⟩⊗Θ_t) = Σ_y |y⟩⊗Θ_{t+1}App^{(t)}_{x,y} → the identity on every path basis vector |x⃗,y⃗⟩; reason: both sides are linear in the path vector; the page states it on inputs |x⟩⊗|x⃗⟩|y⃗⟩
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Claim 5.6, Eq. (5.19), p.66

import Mathlib
import Definitions.Def_PathRecording_fourier
import Definitions.Def_PathRecording_pathOracle

set_option autoImplicit false

namespace PathRecording

open Matrix MeasureTheory

/-- Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Claim 5.6, Eq. (5.19), p.66: `Q_ρ · (|x⟩ ⊗ Θ_t) = Σ_y |y⟩ ⊗ Θ_{t+1} App^{(t)}_{x,y}`,
on every path basis vector `|x⃗, y⃗⟩`: `Q_ρ(|x⟩ ⊗ Θ_t|x⃗,y⃗⟩)` has `|y⟩`-component
`Θ_{t+1}(App^{(t)}_{x,y}|x⃗,y⃗⟩)`. -/
theorem claim_5_6 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {N : ℕ} (ρ : UnitaryRep G N) (t : ℕ) (x : Fin N) (p : PathIdx N t) :
    oracle μ ρ (Pi.single x (thetaVec μ ρ t p)) =
      fun y => theta μ ρ (t + 1) (append t x y *ᵥ Pi.single p 1) := by sorry

end PathRecording
