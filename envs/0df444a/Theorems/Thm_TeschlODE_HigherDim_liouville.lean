-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_liouville
-- name    : TeschlODE.HigherDim.liouville
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:52:08.279213+00:00
-- url     : https://prove2.me/theorems/83b5bd1d-e107-46bb-96bb-49f16bab3981
-- title:
--   Theorem 8.10 (Liouville) — the volume in phase space is preserved under a Hamiltonian flow
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n \times \mathbb{R}^n$ be an open region of phase space with points $(p, q)$, let $H : \Omega \to \mathbb{R}$ be a $C^2$ Hamilton function, and let $\Phi$ be the (local) flow of Hamilton's equations
--   $$\dot q = \frac{\partial H(p, q)}{\partial p}, \qquad \dot p = -\frac{\partial H(p, q)}{\partial q} \qquad (8.43)$$
--   on $\Omega$. Then the volume in phase space is preserved under the flow: for every measurable $U \subseteq \Omega$ and every time $t$ at which all points of $U$ are still alive ($t \in I_x$ for all $x \in U$),
--   $$|\Phi(t, U)| = |U| ,$$
--   where $|\cdot|$ is Lebesgue measure on $\mathbb{R}^{2n}$.
--
--   Liouville's theorem is the basic structural fact of Hamiltonian mechanics: it underlies Poincaré recurrence (Theorem 8.11), statistical mechanics (invariance of the microcanonical measure) and the obstruction to asymptotically stable equilibria in Hamiltonian systems.
--
--   **Formalization Note.** The book states it in one line. The statement reads "Hamiltonian flow" as the flow of $X_H$ for $H \in C^2$ on an open $\Omega$ (the regularity Lemma 8.8 needs for a $C^1$ vector field) and "volume" as Lebesgue measure of any measurable set of points alive at time $t$, a set that may be unbounded and have infinite volume. The chapter's completeness assumption is not needed and is not made; when the flow is complete, the hypothesis on $t$ holds for every $t$. Phase points are pairs `(p, q)` in `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)`, whose `volume` is the product Lebesgue measure.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 241, Theorem 8.10

import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_hamiltonianVectorField

open MeasureTheory

namespace TeschlODE.HigherDim

/-- Teschl, Theorem 8.10 (Liouville), p. 241: the volume in phase space is preserved under a
Hamiltonian flow. `H` is `C²` on the open phase-space region `Ω ⊆ ℝⁿ × ℝⁿ`, `Φ` is the (local)
flow of Hamilton's equations (8.43) on `Ω`; for every measurable `U ⊆ Ω` and every time `t`
at which all points of `U` are still alive, `|Φ(t, U)| = |U|` (Lebesgue measure on `ℝ²ⁿ`). -/
theorem liouville {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hH : ContDiffOn ℝ 2 H Ω)
    (I : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow (hamiltonianVectorField H) Ω I Φ)
    (U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) (hU : MeasurableSet U)
    (hUΩ : U ⊆ Ω) (t : ℝ) (ht : ∀ x ∈ U, t ∈ I x) :
    volume (Φ t '' U) = volume U := by sorry

end TeschlODE.HigherDim
