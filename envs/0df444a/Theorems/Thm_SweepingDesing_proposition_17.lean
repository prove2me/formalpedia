-- Prove2me | Theorems.Thm_SweepingDesing_proposition_17
-- name    : SweepingDesing.proposition_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:16:52.086439+00:00
-- url     : https://prove2.me/theorems/ace69627-245c-46ea-8f57-fd6f068a0ec5
-- title:
--   Proposition 17 — diffeomorphic rescaling of time preserves orbits
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be any set-valued map, $a,b,\rho\in\mathbb R$, and $\gamma\in\mathcal{AC}(S,(a,b))$. Let $\Psi:(0,\rho)\to(a,b)$ be a $C^1$-smooth diffeomorphism with $\Psi'(r)>0$ for all $r\in(0,\rho)$. Then $\tilde\gamma=\gamma\circ\Psi$ is an orbit of the sweeping process defined by $\tilde S=S\circ\Psi$:
--
--   $$
--   \gamma\circ\Psi\in\mathcal{AC}(S\circ\Psi,(0,\rho)).
--   $$
--
--   It allows one to work with a reparametrized sweeping process, in which a desingularizing change of time makes all orbit speeds at most one.
--
--   Differences from the source:
--   - reading: absolutely continuous on a (possibly non-compact) interval I → absolutely continuous on every compact interval [c, d] ⊆ I (IsLocallyAC); reason: the usual W^{1,1}_loc reading for [t, t+δ), [a, b), (a, b) and the pieces J_i; on a compact interval it is absolute continuity on I
--   - encoding: Ψ : (0, ρ) → (a, b) a C¹-smooth diffeomorphism with Ψ′ > 0 → Ψ : ℝ → ℝ, C¹ on (0, ρ), Ψ′ > 0 there, and Ψ maps (0, ρ) bijectively onto (a, b); reason: the inverse is then C¹ by the inverse function theorem; values of Ψ off (0, ρ) play no role
--   - encoding: a curve γ : I → ℝⁿ with −γ̇(t) ∈ N_{S(t)}(γ(t)) for almost every t ∈ I → γ : ℝ → ℝⁿ, and for almost every t ∈ I there is v with HasDerivAt γ v t and −v ∈ N_{S(t)}(γ(t)); reason: values of γ off I play no role; almost every t ∈ I is an interior point of I at which an absolutely continuous curve is differentiable
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 17, p.11

import Mathlib
import Definitions.Def_SweepingDesing_IsACOrbit
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Proposition 17, p.11 (diffeomorphic rescaling of time): let `S : ℝ ⇉ ℝⁿ` be a
multivalued map and `γ ∈ 𝒜𝒞(S, (a, b))`. If `Ψ : (0, ρ) → (a, b)` is a `C¹`-smooth
diffeomorphism with `Ψ'(r) > 0` for all `r ∈ (0, ρ)`, then `γ̃ = γ ∘ Ψ` is an orbit of the
sweeping process defined by `S̃ := S ∘ Ψ`, that is, `γ̃ ∈ 𝒜𝒞(S̃, (0, ρ))`.

**Formalization Note** `Ψ` is a map `ℝ → ℝ` that is `C¹` on `(0, ρ)`, has positive derivative
there and maps `(0, ρ)` bijectively onto `(a, b)` (then its inverse is `C¹` by the inverse
function theorem). Its values off `(0, ρ)` play no role. -/
theorem proposition_17 {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (a b ρ : ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (hγ : IsACOrbit S γ (Ioo a b)) (Ψ : ℝ → ℝ) (hΨ : ContDiffOn ℝ 1 Ψ (Ioo 0 ρ))
    (hΨ' : ∀ r ∈ Ioo 0 ρ, 0 < deriv Ψ r) (hbij : BijOn Ψ (Ioo 0 ρ) (Ioo a b)) :
    IsACOrbit (fun r => S (Ψ r)) (fun r => γ (Ψ r)) (Ioo 0 ρ) := by sorry

end SweepingDesing
