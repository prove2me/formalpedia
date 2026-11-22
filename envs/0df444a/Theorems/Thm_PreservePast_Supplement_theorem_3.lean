-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_3
-- name    : PreservePast.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:33:12.675788+00:00
-- url     : https://prove2.me/theorems/d4b65c2e-a5f9-4981-a16a-f4d592cedfdc
-- title:
--   Theorem 3 — finite-order strong direct product
-- statement:
--   Let $f\subseteq X\times Y\times Z$ be a total relation on finite sets, $\mu=\mu_A\otimes\mu_B$, and $c=\mathrm{sub}(f,\epsilon,\mu)$ the product subdistribution bound. Suppose $0<\epsilon<1/6$ and $c\ge 8$, and put
--   $$C=c\ln 2,\qquad a=-\ln(1-\epsilon),\qquad r=\lceil C/(2a)\rceil .$$
--   For every integer $k\ge1$, a randomized two-party protocol on $\mu^{\otimes k}$ with worst-case communication $B$ bits, whose output is determined by its transcript and coins, has all-coordinate success $s$ satisfying
--   $$\ln s\le\frac{B\ln 2}{r}-\frac{kC}{4r}+\frac{k\ln 2}{r^2}.$$
--   In particular, $B\le kc/8$ implies $s\le(1-\epsilon)^{k/8}$, with no restriction on the number of rounds.
--
--   This is a strong direct-product theorem obtained from the source exponent $\mathcal H_r$ without coordinate-wise extraction.
--
--   **Formalization Note** A randomized protocol is a probability space of coins and, for each coin value, a deterministic protocol tree of depth at most $B$; its success is the average of the deterministic all-coordinate success.
--
--   Differences from the source:
--   - encoding: ln s ≤ B ln 2/r − kC/(4r) + k ln 2/r² → s ≤ exp(B ln 2/r − kC/(4r) + k ln 2/r²); reason: the same inequality for s > 0; for s = 0 Lean's log 0 = 0 would misstate the source's ln 0 = −∞
--   - generalization: a randomized two-party protocol with output determined by its transcript and coins → any family of deterministic protocol trees indexed by a probability space of coins, with success the lower integral of the deterministic success and no measurability requirement; reason: public coins include private coins, and every measurable randomized protocol is such a family with the same success
--   - encoding: c = sub(f, ϵ, μ) with C = c ln 2 and r = ⌈C/(2a)⌉ → c is a real number equal to the extended-real bound; reason: the theorem needs a finite c; the bound is +∞ only when its feasible set is empty
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 3, p.5 (PDF p.7), eq. (7)

import Mathlib
import Definitions.Def_PreservePast_Supplement_subdistBound

open MeasureTheory

namespace PreservePast.Supplement

/-- **Theorem 3 (Finite-order strong direct product).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 3, p.5 (PDF p.7), eq. (7).

Let `f ⊆ X × Y × Z` be a total relation on finite sets, `μ = μ_A ⊗ μ_B`, `c = sub(f, ϵ, μ)`,
`0 < ϵ < 1/6`, `c ≥ 8`, `C = c ln 2`, `a = −ln(1 − ϵ)`, `r = ⌈C/(2a)⌉`. For every `k ≥ 1`, a
randomized protocol on `μ^{⊗k}` with worst-case communication `B` bits has all-coordinate success
`s` with `ln s ≤ B ln 2/r − kC/(4r) + k ln 2/r²`; in particular `B ≤ kc/8` implies
`s ≤ (1 − ϵ)^{k/8}`.

**Formalization Note.** A randomized protocol is a coin space `(Ω, P)` and, for each coin value,
a deterministic protocol tree (the published `PermInvCC.ProtoTree`) of depth at most `B` (this covers public and private coins; the
output is determined by the transcript and the coins). Its success `s` is the `P`-average of the
deterministic all-coordinate success, a lower integral, so no measurability of `ω ↦ π ω` is
required. (7) is stated in the exponentiated form `s ≤ exp(…)`, which is the same inequality for
`s > 0` and is the source's meaning (`ln 0 = −∞`) for `s = 0`, where Lean's `Real.log 0 = 0`
would misstate it. `c` is a real number equal to the `EReal`-valued bound, i.e. the bound is
finite, as `C = c ln 2` and `r` require. -/
theorem theorem_3 {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (f : X → Y → Z → Prop) (hf : ∀ x y, ∃ z, f x y z) (μA : PMF X) (μB : PMF Y)
    (ε c : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 6) (hc : subdistBound f ε μA μB = ((c : ℝ) : EReal))
    (hc8 : 8 ≤ c) (k : ℕ) (hk : 1 ≤ k) (B : ℕ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (π : Ω → PermInvCC.ProtoTree (Fin k → X) (Fin k → Y) (Fin k → Z))
    (hπ : ∀ ω, (π ω).depth ≤ B) :
    (∫⁻ ω, allCoordSuccess f μA μB k (π ω) ∂P).toReal ≤
        Real.exp (B * Real.log 2 / (⌈c * Real.log 2 / (2 * -Real.log (1 - ε))⌉₊ : ℝ)
          - k * (c * Real.log 2) / (4 * (⌈c * Real.log 2 / (2 * -Real.log (1 - ε))⌉₊ : ℝ))
          + k * Real.log 2 / (⌈c * Real.log 2 / (2 * -Real.log (1 - ε))⌉₊ : ℝ) ^ 2) ∧
      ((B : ℝ) ≤ k * c / 8 →
        (∫⁻ ω, allCoordSuccess f μA μB k (π ω) ∂P).toReal ≤ (1 - ε) ^ ((k : ℝ) / 8)) := by sorry

end PreservePast.Supplement
