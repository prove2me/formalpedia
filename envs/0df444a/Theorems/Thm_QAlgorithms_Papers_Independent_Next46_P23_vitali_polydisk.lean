-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_vitali_polydisk
-- name    : QAlgorithms.Papers.Independent.Next46.P23.vitali_polydisk
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:07:08.490975+00:00
-- url     : https://prove2.me/theorems/0fc7654b-cbaa-482e-bd3d-cd7a605eac71
-- title:
--   Theorem B.1
-- statement:
--   Let $n\ge1$, $\epsilon>0$ and $D_\epsilon=\{z\in\mathbb C^n:|z_j|<\epsilon\ \forall j\}$. Let $t$ range over an arbitrary unbounded subset of positive real numbers, and let holomorphic $F_t:D_\epsilon\to\mathbb C$ be uniformly bounded over all $t,z$. If $F_t$ converges at every real point in this polydisk, then it converges at every complex point to a holomorphic function $F$. For every mixed partial derivative and every compact $K\subset D_\epsilon$, $$\partial^kF_t\longrightarrow\partial^kF\quad\text{uniformly on }K.$$ The empty derivative includes the functions themselves; the real-slice limits uniquely determine the holomorphic extension.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 163, Theorem B.1

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- TheoremB.1, full mixed-derivative compact-uniform convergence, source PDF p.163.
The index set is an arbitrary unbounded subset of positive real times. -/
theorem vitali_polydisk (n : ℕ) (hn : 1 ≤ n) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (times : Set ℝ) (hpositive : ∀ t ∈ times, 0 < t)
    (hunbounded : ∀ R : ℝ, ∃ t ∈ times, R ≤ t)
    (F : times → (Fin n → ℂ) → ℂ)
    (hanalytic : ∀ t, AnalyticOnNhd ℂ (F t) (polydisk n epsilon))
    (hbounded : ∃ C : ℝ, ∀ t, ∀ z ∈ polydisk n epsilon, ‖F t z‖ ≤ C)
    (hreal : ∀ x : Fin n → ℝ, (∀ j, |x j| < epsilon) →
      ∃ l : ℂ, Tendsto (fun t => F t (fun j => (x j : ℂ)))
        (Filter.comap Subtype.val atTop) (nhds l)) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ G (polydisk n epsilon) ∧
      (∀ z ∈ polydisk n epsilon, Tendsto (fun t => F t z)
        (Filter.comap Subtype.val atTop) (nhds (G z))) ∧
      (∀ js : List (Fin n), ∀ K : Set (Fin n → ℂ),
        IsCompact K → K ⊆ polydisk n epsilon →
        TendstoUniformlyOn (fun t => complexMixedPartial js (F t)) (complexMixedPartial js G)
          (Filter.comap Subtype.val atTop) K) ∧
      (∀ Galt : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Galt (polydisk n epsilon) →
        (∀ x : Fin n → ℝ, (∀ j, |x j| < epsilon) →
          Tendsto (fun t => F t (fun j => (x j : ℂ)))
            (Filter.comap Subtype.val atTop) (nhds (Galt (fun j => (x j : ℂ))))) →
        Set.EqOn Galt G (polydisk n epsilon)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
