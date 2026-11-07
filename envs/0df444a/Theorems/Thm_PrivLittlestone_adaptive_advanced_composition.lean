-- Prove2me | Theorems.Thm_PrivLittlestone_adaptive_advanced_composition
-- name    : PrivLittlestone.adaptive_advanced_composition
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:30:25.857807+00:00
-- url     : https://prove2.me/theorems/ea13c262-b448-454c-ac0e-bf86d52f47f4
-- title:
--   Adaptive advanced composition [KOV15] with interleaved identical kernels, as used in Lemma B.3
-- statement:
--   Consider two $n$-step sequential interactions with kernel families $\kappa^0, \kappa^1$ indexed by the common history. Suppose that at every history either the two kernels coincide (a zero-cost step), or they are $(\varepsilon_0, \delta_0)$-indistinguishable in both directions, with $0 \le \varepsilon_0 \le 1$ and $\delta_0 \ge 0$, and that along every path at most $k$ steps have non-identical kernels. Then for every $0 < \tilde\delta < 1$ the two transcript laws $P^0, P^1$ satisfy, for every event $E$,
--   $$
--   P^0(E) \le e^{\varepsilon'} P^1(E) + \delta', \qquad P^1(E) \le e^{\varepsilon'} P^0(E) + \delta',
--   $$
--   where
--   $$
--   \varepsilon' = \sqrt{2k\log(1/\tilde\delta)}\,\varepsilon_0 + 2k\varepsilon_0^2, \qquad \delta' = \tilde\delta + k\delta_0 .
--   $$
--
--   The paper invokes this for the comparison of the actual transcript law with the hybrid law in Lemma B.3, with $k = Km$, $\varepsilon_0 = \varepsilon_s$, $\delta_0 = 3\tau$.
--
--   **Formalization Note** Imported: the paper cites [KOV15] and does not display the bound. Kernels are probability mass functions on an arbitrary output type, and events are arbitrary sets. The term $2k\varepsilon_0^2$ bounds the usual $k\varepsilon_0(e^{\varepsilon_0} - 1)$ because $\varepsilon_0 \le 1$.
--
--   Differences from the source:
--
--   - reading: adaptive advanced composition over at most Km candidate releases, with interleaved zero-cost common kernels [KOV15] → the explicit bound ε' = √(2k log(1/δ̃)) ε₀ + 2kε₀², δ' = δ̃ + kδ₀ for history-dependent PMF kernels, at most k non-identical steps per path; reason: the paper cites the result without displaying it; this form gives exactly ε_c and δ_c of Lemma B.3 with k = Km, ε₀ = ε_s, δ₀ = 3τ
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), proof of Lemma B.3, p.23 (citing [KOV15])

import Mathlib
import Definitions.Def_PrivLittlestone_seqPMF

namespace PrivLittlestone

open Classical in
/-- **Adaptive advanced composition [KOV15]**, in the form used in the proof of Lemma B.3 (He–He,
*Private Online Learning of Littlestone Classes and Matroid Flats*, STOC 2027 submission
manuscript (sha256 21480556…c562), proof of Lemma B.3, p.23: "At every common history, the
candidate kernels are `(ε_s, 3τ)`-private by hypothesis. Adaptive advanced composition over at
most `Km` candidate releases therefore makes this pair `(ε_c, δ_c)`-private in both directions
[KOV15]. The interleaved common threshold kernels may depend on the history; their equality makes
them zero-cost transitions"). Two `n`-step sequential interactions with kernel families `κ₀, κ₁`
indexed by the common history: at every history either the two kernels coincide, or they are
`(ε₀, δ₀)`-indistinguishable in both directions, with `0 ≤ ε₀ ≤ 1`; along every path at most `k`
steps have non-identical kernels. Then for every `0 < δ̃ < 1` the two transcript laws are
`(ε', δ')`-indistinguishable in both directions, with `ε' = √(2k log(1/δ̃)) ε₀ + 2kε₀²` and
`δ' = δ̃ + kδ₀`.

**Formalization Note** Imported: cited, not proved, in the paper. Outputs form an arbitrary type
and kernels are probability mass functions (countable support); events are all sets.
`2kε₀²` bounds the usual `kε₀(e^{ε₀} − 1)` because `ε₀ ≤ 1`. -/
theorem adaptive_advanced_composition {α : Type*} (κ₀ κ₁ : (i : ℕ) → (Fin i → α) → PMF α)
    (n k : ℕ) (ε₀ δ₀ δt : ℝ) (hε₀ : 0 ≤ ε₀) (hε₀1 : ε₀ ≤ 1) (hδ₀ : 0 ≤ δ₀) (hδt : 0 < δt)
    (hδt1 : δt < 1)
    (hstep : ∀ i : ℕ, i < n → ∀ h : Fin i → α, κ₀ i h = κ₁ i h ∨
      ∀ E : Set α,
        (κ₀ i h).toOuterMeasure E ≤
            ENNReal.ofReal (Real.exp ε₀) * (κ₁ i h).toOuterMeasure E + ENNReal.ofReal δ₀ ∧
          (κ₁ i h).toOuterMeasure E ≤
            ENNReal.ofReal (Real.exp ε₀) * (κ₀ i h).toOuterMeasure E + ENNReal.ofReal δ₀)
    (hcount : ∀ w : Fin n → α,
      (Finset.univ.filter fun i : Fin n =>
        κ₀ i (fun j => w (Fin.castLE i.isLt.le j)) ≠ κ₁ i (fun j => w (Fin.castLE i.isLt.le j))).card
        ≤ k) :
    ∀ E : Set (Fin n → α),
      (seqPMF κ₀ n).toOuterMeasure E ≤
          ENNReal.ofReal (Real.exp (Real.sqrt (2 * k * Real.log (1 / δt)) * ε₀ + 2 * k * ε₀ ^ 2)) *
            (seqPMF κ₁ n).toOuterMeasure E + ENNReal.ofReal (δt + k * δ₀) ∧
        (seqPMF κ₁ n).toOuterMeasure E ≤
          ENNReal.ofReal (Real.exp (Real.sqrt (2 * k * Real.log (1 / δt)) * ε₀ + 2 * k * ε₀ ^ 2)) *
            (seqPMF κ₀ n).toOuterMeasure E + ENNReal.ofReal (δt + k * δ₀) := by sorry

end PrivLittlestone
