-- Prove2me | Theorems.Thm_SweepingDesing_theoremA
-- name    : SweepingDesing.theoremA
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:18:57.623131+00:00
-- url     : https://prove2.me/theorems/90c8a0a9-03e7-4616-839b-83672bd1c815
-- title:
--   Theorem A — desingularization ⇔ length control ⇔ bounded piecewise lengths ⇔ integrable oriented talweg (corrected: c) quantifies over every $b'\in(a,b]$)
-- statement:
--   Let $S:\mathbb R\rightrightarrows\mathbb R^n$ be a smooth sweeping process with bounded values that satisfies the existence assumption (A1), and let $a\in\mathcal T$ (that is, $a\in\operatorname{dom}(S)$, $a<\sup\operatorname{dom}(S)$, and (A2), (A3) hold at $a$; typically $a$ is a critical value for $D^*S$). The following assertions are equivalent.
--
--   1. **(Desingularization of the coderivative)** There exist $b>a$, $\rho>0$ and a homeomorphism $\Psi:[0,\rho]\to[a,b]$, which is a $C^1$-diffeomorphism between $(0,\rho)$ and $(a,b)$ with $\Psi'(r)>0$ for every $r\in(0,\rho)$, such that
--   $$\|D^*(S\circ\Psi)(r,x)|^+\le1\qquad\text{for all }r\in(0,\rho)\text{ and all }x\in S(\Psi(r)).$$
--   2. **(Uniform length control for absolutely continuous orbits)** There exist $b>a$ and an increasing continuous function $\sigma:[a,b]\to\mathbb R_+$ with $\sigma(a)=0$ such that for all $a\le t_1<t_2\le b$ and every $\gamma\in\mathcal{AC}(S,[t_1,t_2])$,
--   $$\ell(\gamma)\le\sigma(t_2)-\sigma(t_1).$$
--   3. **(Length bound for piecewise absolutely continuous orbits, corrected)** There exist $b>a$ and $M>0$ such that for every $b'\in(a,b]$ and every $\gamma\in\mathcal{PAC}(S,[a,b'])$,
--   $$\ell(\gamma)\le M.$$
--   4. **(Integrability of the oriented talweg)** There exists $b>a$ such that
--   $$\int_a^b\varphi^\uparrow(t)\,dt<\infty.$$
--
--   This is the sweeping-process analogue, without o-minimality, of the characterization of the Kurdyka–Łojasiewicz inequality by length bounds of subgradient curves and by integrability of the talweg.
--
--   **Formalization Note** In clause 1, $\Psi$ is a real function, continuous and strictly increasing on $[0,\rho]$ with $\Psi(0)=a$, $\Psi(\rho)=b$, and $C^1$ with positive derivative on $(0,\rho)$. Moduli, lengths and the integral take values in $[0,+\infty]$.
--
--   Differences from the source:
--   - encoding: smooth sweeping process (Definition 10): a closed connected C¹ submanifold of ℝⁿ⁺¹ of dimension at most n, or a connected full-dimensional manifold with boundary whose boundary is a C¹ manifold of dimension n (closed graph, §3.1) → IsSmoothSweepingProcess: the graph is closed and connected and is cut out near each of its points by a C¹ submersion onto ℝ^{n+1−k} with one k ≤ n, or near each of its frontier points by {g ≤ 0} with g C¹ and dg ≠ 0; reason: the standard local description of C¹ embedded submanifolds and of full-dimensional closed regions with C¹ boundary; the same sets
--   - encoding: moduli and talwegs with values in ℝ ∪ {+∞}, sup ∅ = 0 → values in ℝ≥0∞ (ENNReal.ofReal a = a⁺), empty supremum 0; reason: the values are nonnegative; [0, +∞] carries the usual topology of ℝ ∪ {+∞} restricted to it
--   - encoding: ℝⁿ⁺¹ with its Euclidean norm, time first → ℝ × EuclideanSpace ℝ (Fin n) with the max of the two norms; reason: normal cones, ∂𝒮 and Pompeiu–Hausdorff continuity do not change under an equivalent norm
--   - reading: absolutely continuous on a (possibly non-compact) interval I → absolutely continuous on every compact interval [c, d] ⊆ I (IsLocallyAC); reason: the usual W^{1,1}_loc reading for [t, t+δ), [a, b), (a, b) and the pieces J_i; on a compact interval it is absolute continuity on I; in this theorem the reading changes no instance, because an orbit of (A1) restricts to [t, t+δ/2], and adding to D the endpoints of I and a sequence of points exhausting each J_i makes a curve of IsPAC absolutely continuous on every piece, with the same length
--   - encoding: t̄ ∈ dom(S) with t̄ < T = sup dom(S) (resp. t̄ ∈ dom(S) ∖ {T}) → S(t̄) ≠ ∅ and S(s) ≠ ∅ for some s > t̄; reason: T may be +∞; for t̄ ∈ dom(S) these are the same condition
--   - correction: c) There exist b > a and M > 0 such that for every γ ∈ PAC(S, [a, b]) we have ℓ(γ) ≤ M → there exist b > a and M > 0 such that ℓ(γ) ≤ M for every b′ ∈ (a, b] and every γ ∈ PAC(S, [a, b′]); reason: as printed, c) can hold vacuously while d) fails. Take n = 2, a C² convex coercive f₀ whose minimum value r̄ fails the KL inequality (Bolte–Daniilidis–Ley–Mazet, §4.3, cited on p.2), a fat Cantor set C ⊂ (r̄+3, r̄+4), and a C² increasing ψ with ψ(s) = s for s ≤ r̄+3, 0 ≤ ψ′ ≤ 1, ψ′ = 0 exactly on C; put S(t) = (ψ ∘ f₀)⁻¹(t). The graph is a closed connected C¹ hypersurface, the values are compact, (A1) holds, and a = r̄ ∈ 𝒯; d) fails because sup_{f₀ = t} 1/‖∇f₀‖ is not integrable near r̄. With b = r̄+5, PAC(S, [a, b]) is empty (an orbit crossing the null set ψ(C) off its jump set would make the AC map f₀ ∘ γ = ψ⁻¹ send a null set onto a set of positive measure, against Lusin's property (N)), so printed c) holds. The proof of c) ⇒ d) on p.14 shrinks b, and b) ⇒ c) gives the corrected clause with M = σ(b)
--   - reading: an increasing continuous function σ : [a, b] → ℝ⁺ → σ continuous and strictly increasing on [a, b] (StrictMonoOn); reason: the σ = Ψ⁻¹ built in the proof is strictly increasing, as is the σ of Theorem 1(b), p.2; σ ≥ 0 follows from σ(a) = 0; a merely nondecreasing σ can be replaced by σ(t) + t − a, so the two readings of b) are equivalent
--   - encoding: Ψ : [0, ρ] → [a, b] a homeomorphism that is a C¹-diffeomorphism (0, ρ) → (a, b) with Ψ′ > 0, and S ∘ Ψ → Ψ : ℝ → ℝ continuous and strictly increasing on [0, ρ], Ψ(0) = a, Ψ(ρ) = b, C¹ on (0, ρ) with Ψ′ > 0; S ∘ Ψ is r ↦ S(Ψ(r)); reason: an increasing continuous bijection of compact intervals is a homeomorphism and the inverse of a C¹ map with Ψ′ > 0 is C¹; the normal cone at r ∈ (0, ρ) is local, so values of Ψ off [0, ρ] play no role
--   - encoding: ∫_a^b φ↑(t) < ∞, with φ↑ defined on dom(S) → the lower Lebesgue integral over (a, b) of the ℝ≥0∞-valued φ↑, which is 0 off dom(S); reason: every clause is preserved when b decreases, and a < sup dom(S) with dom(S) an interval, so the value of φ↑ off dom(S) changes no instance
--   - encoding: S with bounded values → Bornology.IsBounded (S t) for every t ∈ ℝ; reason: the same condition
--   - encoding: a curve γ : I → ℝⁿ with −γ̇(t) ∈ N_{S(t)}(γ(t)) for almost every t ∈ I → γ : ℝ → ℝⁿ, and for almost every t ∈ I there is v with HasDerivAt γ v t and −v ∈ N_{S(t)}(γ(t)); reason: values of γ off I play no role; almost every t ∈ I is an interior point of I at which an absolutely continuous curve is differentiable
--   - encoding: ℓ(γ) := ∫_I ‖γ̇(t)‖ dt, compared with real bounds → curveLength γ I = ∫⁻ t in I, ‖deriv γ t‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: deriv γ is the derivative at almost every t ∈ I and the integrand is nonnegative, so this is the same integral, with +∞ allowed; jumps do not count
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Theorem A, pp.9–10 (statement p.9, clauses c)–d) p.10)

import Mathlib
import Definitions.Def_SweepingDesing_IsSmoothSweepingProcess
import Definitions.Def_SweepingDesing_ExistenceAssumption
import Definitions.Def_SweepingDesing_calT
import Definitions.Def_SweepingDesing_orientedModulus
import Definitions.Def_SweepingDesing_orientedTalweg
import Definitions.Def_SweepingDesing_IsACOrbit
import Definitions.Def_SweepingDesing_IsPACOrbit
import Definitions.Def_SweepingDesing_curveLength
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Theorem A, pp.9–10, with clause c) corrected. Let `S : ℝ ⇉ ℝⁿ` be a smooth sweeping
process with bounded values that satisfies (A1). Let `a ∈ 𝒯`. The following are equivalent:
* a) (desingularization of the coderivative) there exist `b > a`, `ρ > 0` and a homeomorphism
  `Ψ : [0, ρ] → [a, b]`, which is a `C¹`-diffeomorphism between `(0, ρ)` and `(a, b)` with
  `Ψ'(r) > 0` for every `r ∈ (0, ρ)`, such that `‖D*(S ∘ Ψ)(r, x)|⁺ ≤ 1` for all `r ∈ (0, ρ)` and
  all `x ∈ S(Ψ(r))`;
* b) (uniform length control for the absolutely continuous orbits) there exist `b > a` and an
  increasing continuous `σ : [a, b] → ℝ₊` with `σ(a) = 0` such that `ℓ(γ) ≤ σ(t₂) - σ(t₁)` for
  every `a ≤ t₁ < t₂ ≤ b` and `γ ∈ 𝒜𝒞(S, [t₁, t₂])`;
* c) (length bound for the piecewise absolutely continuous orbits; **corrected**) there exist
  `b > a` and `M > 0` such that `ℓ(γ) ≤ M` for every `b' ∈ (a, b]` and every
  `γ ∈ 𝒫𝒜𝒞(S, [a, b'])` (the paper has only `b' = b`, which is false: `𝒫𝒜𝒞(S, [a, b])` can be
  empty for large `b` while d) fails);
* d) (integrability of the talweg) there exists `b > a` with `∫_a^b φ↑(t) dt < ∞`.

**Formalization Note** a): `Ψ` is continuous and strictly increasing on `[0, ρ]` with `Ψ(0) = a`,
`Ψ(ρ) = b`, and `C¹` with positive derivative on `(0, ρ)`; `S ∘ Ψ` is `r ↦ S(Ψ(r))`. b): "increasing"
is read as strictly increasing; `σ ≥ 0` follows from `σ(a) = 0`. Lengths are in `[0, +∞]`. d) is
the lower Lebesgue integral of the `[0, +∞]`-valued `φ↑` over `(a, b)`. -/
theorem theoremA {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (hS : IsSmoothSweepingProcess S)
    (hbdd : ∀ t, Bornology.IsBounded (S t)) (hA1 : ExistenceAssumption S) (a : ℝ)
    (ha : a ∈ calT S) :
    List.TFAE
      [∃ b > a, ∃ ρ > (0 : ℝ), ∃ Ψ : ℝ → ℝ, ContinuousOn Ψ (Icc 0 ρ) ∧ StrictMonoOn Ψ (Icc 0 ρ) ∧
          Ψ 0 = a ∧ Ψ ρ = b ∧ ContDiffOn ℝ 1 Ψ (Ioo 0 ρ) ∧ (∀ r ∈ Ioo 0 ρ, 0 < deriv Ψ r) ∧
          ∀ r ∈ Ioo 0 ρ, ∀ x ∈ S (Ψ r), orientedModulus (fun r' => S (Ψ r')) r x ≤ 1,
        ∃ b > a, ∃ σ : ℝ → ℝ, ContinuousOn σ (Icc a b) ∧ StrictMonoOn σ (Icc a b) ∧ σ a = 0 ∧
          ∀ t₁ t₂ : ℝ, a ≤ t₁ → t₁ < t₂ → t₂ ≤ b → ∀ γ : ℝ → EuclideanSpace ℝ (Fin n),
            IsACOrbit S γ (Icc t₁ t₂) → curveLength γ (Icc t₁ t₂) ≤ ENNReal.ofReal (σ t₂ - σ t₁),
        ∃ b > a, ∃ M > (0 : ℝ), ∀ b' ∈ Ioc a b, ∀ γ : ℝ → EuclideanSpace ℝ (Fin n),
          IsPACOrbit S γ (Icc a b') → curveLength γ (Icc a b') ≤ ENNReal.ofReal M,
        ∃ b > a, ∫⁻ t in Ioo a b, orientedTalweg S t < ⊤] := by sorry

end SweepingDesing
