-- Prove2me | Theorems.Thm_TeschlODE_HigherDim_poincare_recurrence
-- name    : TeschlODE.HigherDim.poincare_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T16:31:54.899878+00:00
-- url     : https://prove2.me/theorems/61d4c832-96e2-48d9-afb5-b3b079d75316
-- title:
--   Theorem 8.11 (Poincaré) — recurrence for a volume preserving bijection of a bounded region
-- statement:
--   Let $D \subseteq \mathbb{R}^n$ be a bounded measurable region and let $\Phi : D \to D$ be a **volume preserving bijection**: $\Phi$ maps $D$ bijectively onto $D$, and for every measurable $A \subseteq D$ the image $\Phi(A)$ is measurable with $|\Phi(A)| = |A|$ (Lebesgue measure). Then every neighborhood $U \subseteq D$ contains a point returning to $U$:
--   $$\exists\, x \in U,\ \exists\, k \in \mathbb{N},\ k \ge 1 :\quad \Phi^k(x) \in U .$$
--
--   Combined with Liouville's theorem 8.10, it says that a Hamiltonian flow confined to a bounded region returns arbitrarily close to where it started.
--
--   **Formalization Note.** "Region" is read as a measurable set (more general than an open connected one); "any neighborhood $U \subseteq D$" as any $U$ that is a neighborhood of some point $y$ ($U \in \mathcal{N}(y)$), so in particular $U$ is nonempty — without nonemptiness the claim is false. $\mathbb{N}$ starts at $1$ in the book; $k \ge 1$ is explicit, since $k = 0$ would make the statement trivial. $\Phi$ is a map $\mathbb{R}^n \to \mathbb{R}^n$ whose values off $D$ are irrelevant; $\Phi^k$ is the $k$-fold iterate.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 241, Theorem 8.11

import Mathlib

open MeasureTheory

namespace TeschlODE.HigherDim

/-- Teschl, Theorem 8.11 (Poincaré), p. 241: let `Φ` be a volume preserving bijection of a
bounded (measurable) region `D ⊆ ℝⁿ`. Then every neighborhood `U ⊆ D` (of any point) contains a
point `x` returning to `U`: `Φⁿ(x) ∈ U` for some `n ≥ 1`. -/
theorem poincare_recurrence {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hD : MeasurableSet D) (hDb : Bornology.IsBounded D)
    (Φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hbij : Set.BijOn Φ D D)
    (hvol : ∀ A ⊆ D, MeasurableSet A → MeasurableSet (Φ '' A) ∧ volume (Φ '' A) = volume A) :
    ∀ y : EuclideanSpace ℝ (Fin n), ∀ U ∈ nhds y, U ⊆ D →
      ∃ x ∈ U, ∃ k : ℕ, 1 ≤ k ∧ Φ^[k] x ∈ U := by sorry

end TeschlODE.HigherDim
