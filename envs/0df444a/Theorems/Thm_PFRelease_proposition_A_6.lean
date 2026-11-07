-- Prove2me | Theorems.Thm_PFRelease_proposition_A_6
-- name    : PFRelease.proposition_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:00.448287+00:00
-- url     : https://prove2.me/theorems/213e2085-d355-4307-967b-9a8af95e6387
-- title:
--   Proposition A.6 — two-stage composition
-- statement:
--   Let $\varepsilon_1,\varepsilon_2\ge0$ and $\delta_1,\delta_2\in[0,1]$. Let $A,A'$ be random variables over a countable set $U$ with $A\approx_{\varepsilon_2,\delta_2}A'$, and let $P_u,P'_u$ be distributions with $P_u\approx_{\varepsilon_1,\delta_1}P'_u$ for each $u\in U$. If $B$ has distribution $P_u$ conditionally on $A=u$, and $B'$ has distribution $P'_u$ conditionally on $A'=u$, whenever these events have positive probability, then
--   $$
--   (A,B)\approx_{\varepsilon_1+\varepsilon_2,\,\delta_1+\delta_2}(A',B'),
--   \qquad\text{and in particular}\qquad
--   B\approx_{\varepsilon_1+\varepsilon_2,\,\delta_1+\delta_2}B'.
--   $$
--
--   It is the composition step of the PFR theorem, with the filtered data outside the changed slot as the first stage.
--
--   **Formalization Note** The law of $(A,B)$ is $\sum_u\Pr[A=u]\,\delta_u\otimes P_u$ and the law of $B$ is $\sum_u\Pr[A=u]\,P_u$; $U$ has measurable singletons.
--
--   Differences from the source:
--   - encoding: random variables $A,B$ with $B\mid A=u\sim P_u$ whenever $\Pr[A=u]>0$ → the law of $A$ on $U$ and the joint law $\sum_u\Pr[A=u]\,\delta_u\otimes P_u$ (marginal $\sum_u\Pr[A=u]P_u$); reason: these are exactly the laws of all such pairs; terms with $\Pr[A=u]=0$ vanish
--   - encoding: a countable set $U$ → a countable type with a measurable space in which singletons are measurable; reason: events of $U$ and of $U\times Y$ are measurable sets
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Proposition A.6, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace PFRelease

/-- **Proposition A.6 (Two-stage composition)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Proposition A.6, p.27 = PDF p.29).
Given `ε₁, ε₂ ≥ 0`, `δ₁, δ₂ ∈ [0, 1]`, random variables `A, A′` over a countable set `U` with
`A ≈_{ε₂,δ₂} A′`, and distributions `P_u, P′_u` with `P_u ≈_{ε₁,δ₁} P′_u` for each `u ∈ U`: if `B` has
distribution `P_u` conditionally on `A = u`, and `B′` has distribution `P′_u` conditionally on
`A′ = u`, whenever these events have positive probability, then `(A, B) ≈_{ε₁+ε₂,δ₁+δ₂} (A′, B′)`,
and in particular `B ≈_{ε₁+ε₂,δ₁+δ₂} B′`.

**Formalization Note** `A, A′` are represented by their laws on `U` (countable, measurable
singletons). The law of `(A, B)` is `Σ_u Pr[A = u] · δ_u ⊗ P_u`, written as the image of `P_u`
under `y ↦ (u, y)`; the law of `B` is `Σ_u Pr[A = u] · P_u`. These are exactly the laws of all
pairs with the stated conditional laws (the terms with `Pr[A = u] = 0` vanish). -/
theorem proposition_A_6 {U Y : Type*} [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
    [MeasurableSpace Y] (ε₁ ε₂ δ₁ δ₂ : ℝ) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hδ₁0 : 0 ≤ δ₁)
    (hδ₁1 : δ₁ ≤ 1) (hδ₂0 : 0 ≤ δ₂) (hδ₂1 : δ₂ ≤ 1) (A A' : Measure U) [IsProbabilityMeasure A]
    [IsProbabilityMeasure A'] (P P' : U → Measure Y) (hP : ∀ u, IsProbabilityMeasure (P u))
    (hP' : ∀ u, IsProbabilityMeasure (P' u)) (hA : Indist A A' ε₂ δ₂)
    (hPu : ∀ u, Indist (P u) (P' u) ε₁ δ₁) :
    Indist (Measure.sum fun u => A {u} • (P u).map (Prod.mk u))
        (Measure.sum fun u => A' {u} • (P' u).map (Prod.mk u)) (ε₁ + ε₂) (δ₁ + δ₂) ∧
      Indist (Measure.sum fun u => A {u} • P u) (Measure.sum fun u => A' {u} • P' u)
        (ε₁ + ε₂) (δ₁ + δ₂) := by sorry

end PFRelease
