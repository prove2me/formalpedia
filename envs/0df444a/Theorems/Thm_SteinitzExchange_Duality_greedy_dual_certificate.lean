-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_greedy_dual_certificate
-- name    : SteinitzExchange.Duality.greedy_dual_certificate
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T15:38:04.075692+00:00
-- url     : https://prove2.me/theorems/ebdc0756-4950-42f2-8a89-8be67326a622
-- title:
--   Greedy dual certificate for a submodular set function: a nonnegative weight attains its maximum over the submodular polyhedron, with weak duality (SteinitzExchange, Lemma 6.3 submodular twin)
-- statement:
--   Greedy dual certificate (Murota 1996, Lemma 6.3), submodular twin: let V be a nonempty finite type and f : Finset V → ℝ submodular (f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) with f ∅ = 0. For every nonnegative weight z : V → ℝ, the greedy vector x* — sort V = {v₁,…,vₙ} by z descending and set x*_{vᵢ} = f{v₁..vᵢ} − f{v₁..vᵢ₋₁} — lies in the submodular polyhedron P = {x | x(X) ≤ f X for all X} and maximizes the linear function ∑_v z_v x_v over P; equivalently the Lovász value f̂(z) equals max{∑_v z_v x_v | x ∈ P}. Weak duality: for any dual-feasible λ : Finset V → ℝ (λ ≥ 0 and ∑_X λ_X 1_X = z as functions on V), every y ∈ P satisfies ∑_v z_v y_v ≤ ∑_X λ_X f_X, so in particular ∑_X λ_X f_X ≥ f̂(z). The supermodular twin (∑_Y μ_Y g_Y ≤ ĝ(z) for supermodular g) is the same statement applied to −g. Mission use: the greedy dual-cert half of the real-case assembly of Frank's discrete separation (Theorem 6.5), feeding the dual infeasibility certificate of SteinitzExchange.Duality.farkas_affine_form1 (84e2d072); sibling of SteinitzExchange.Duality.frank_separation_real (ce70432e) and SteinitzExchange.Duality.frank_separation_integer (1a78521e).
-- source:
--   Murota 1996 (Discrete Convex Analysis / Submodular Systems), Lemma 6.3 (greedy dual certificate), submodular twin; supermodular twin by negation. Decomposition child of SteinitzExchange.Duality.frank_discrete_separation (f6a72521-28fb-44ad-8ba3-a458fc272560); sibling of frank_separation_real (Thm 6.5 conjunct 1, ce70432e-0b7b-42f5-bbd8-20ffa37343e8) and farkas_affine_form1 (deep input F, 84e2d072-a88f-42fb-9cc9-cfa15b2bb6ba). See ~/workspace/p2m_harness/triage_steinitz_frank_separation.md section 3, item G.

import Mathlib

namespace SteinitzExchange.Duality

/-- **Greedy dual certificate** (Murota 1996, Lemma 6.3, submodular twin): let
`f : Finset V → ℝ` be submodular with `f ∅ = 0`. For every nonnegative weight
`z : V → ℝ`, the greedy vector `x*` — sort `V = {v₁,…,vₙ}` by `z` descending
and set `x*_{vᵢ} = f{v₁..vᵢ} − f{v₁..vᵢ₋₁}` — lies in the submodular
polyhedron `P = {x | x(X) ≤ f X ∀ X}` and maximizes `∑ v, z v * x v` over `P`;
equivalently the Lovász value `f̂(z)` equals `max {∑ v, z v * x v | x ∈ P}`.
Weak duality: for any dual-feasible `λ : Finset V → ℝ` (`λ ≥ 0`,
`∑_X λ X · 1_X = z` as functions on `V`), every `y ∈ P` satisfies
`∑ v, z v * y v ≤ ∑ X, λ X * f X`, hence `∑ X, λ X * f X ≥ f̂(z)`.
The supermodular twin (`∑_Y μ_Y g Y ≤ ĝ(z)` for supermodular `g`) is the same
statement applied to `−g`. Mission use: the greedy dual-cert half of
`SteinitzExchange.Duality.frank_separation_real`
(ce70432e-0b7b-42f5-bbd8-20ffa37343e8), feeding the dual infeasibility
certificate of `SteinitzExchange.Duality.farkas_affine_form1`
(84e2d072-a88f-42fb-9cc9-cfa15b2bb6ba), inside the real-case assembly of
Theorem 6.5 (`frank_discrete_separation`, f6a72521-28fb-44ad-8ba3-a458fc272560).
Stated without proof. -/
theorem greedy_dual_certificate {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (f : Finset V → ℝ)
    (hf : ∀ X Y : Finset V, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y)
    (hf0 : f ∅ = 0) :
    ∀ z : V → ℝ, (∀ v : V, 0 ≤ z v) →
      ∃ x : V → ℝ,
        (∀ X : Finset V, Finset.sum X (fun v => x v) ≤ f X) ∧
        (∀ y : V → ℝ, (∀ X : Finset V, Finset.sum X (fun v => y v) ≤ f X) →
          Finset.sum Finset.univ (fun v => z v * y v) ≤
            Finset.sum Finset.univ (fun v => z v * x v)) ∧
        (∀ lam : Finset V → ℝ, (∀ X : Finset V, 0 ≤ lam X) →
          (∀ v : V, Finset.sum Finset.univ (fun X => lam X * (if v ∈ X then (1 : ℝ) else 0)) = z v) →
          ∀ y : V → ℝ, (∀ X : Finset V, Finset.sum X (fun v => y v) ≤ f X) →
            Finset.sum Finset.univ (fun v => z v * y v) ≤
              Finset.sum Finset.univ (fun X => lam X * f X)) := by
  sorry

end SteinitzExchange.Duality
