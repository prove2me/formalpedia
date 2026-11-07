-- Prove2me | Theorems.Thm_QPSpinParisi_lemma_3_3
-- name    : QPSpinParisi.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:09:35.266198+00:00
-- url     : https://prove2.me/theorems/2160c14e-a727-45d5-9fac-7800218a58e7
-- title:
--   Lemma 3.3 — $m^Z_n-\varepsilon(\beta)\le A^Z_n(\beta)/\beta\le m^Z_n$ (3.8), and equal limits
-- statement:
--   There is a deterministic function $\varepsilon(\beta)$, with $\varepsilon(\beta)\to0$ as $\beta\to\infty$, independent of $n$, such that for $Z=X_n$ or $Z=Y_n$,
--   $$m^Z_n-\varepsilon(\beta)\le\frac1\beta A^Z_n(\beta)\le m^Z_n.\tag{3.8}$$
--   Suppose that for every fixed $\beta>0$ the limit $F(\beta):=\lim_{n\to\infty}\frac1\beta A^Y_n(\beta)$ exists. Then
--   $$\lim_{n\to\infty}m^X_n=\lim_{n\to\infty}m^Y_n=\lim_{\beta\to\infty}F(\beta).$$
--   This is the passage from positive temperature to the ground state, uniformly in $n$.
--
--   Differences from the source:
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - generalization: no integrability statement → integrability of the integrands is also asserted; reason: a default value of a Bochner integral could otherwise enter; the source's claim follows by dropping the clause
--   - encoding: "$\lim=\lim=\lim$" → one number $L$ with three limits to it; reason: the same statement; the existence of the limits is part of the source's claim
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.3, p.13 (PDF p.13)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_AX
import Definitions.Def_QPSpinParisi_AY
import Definitions.Def_QPSpinParisi_mX
import Definitions.Def_QPSpinParisi_mY

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Lemma 3.3, p.13, PDF p.13: there is a deterministic `ε(β) → 0`, independent of `n` and of the realization, with
`m^Z_n - ε(β) ≤ A^Z_n(β)/β ≤ m^Z_n` for `Z = X_n` and `Z = Y_n` (3.8); and if `F(β) = lim_n A^Y_n(β)/β` exists for every fixed `β > 0`, then
`lim_n m^X_n = lim_n m^Y_n = lim_{β→∞} F(β)`.

**Formalization Note** The integrands of `A^Z_n` and `m^Z_n` are stated to be integrable, so the bounds are not about default values
of a Bochner integral. The source's `F` is `G` here, since `F` names the realizations. -/
theorem lemma_3_3 (c : ℕ → ℝ) (hc : MixHyp c) :
    (∃ ε : ℝ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ β : ℝ, 0 < β → ∀ n : ℕ, 1 ≤ n →
      (Integrable (fun α => Real.log (∫ s, Real.exp (β * Xn c n α s) ∂(RGGDetect.prior n 3))) (gaussMeas n) ∧
        Integrable (fun α => sSup (range (Xn c n α))) (gaussMeas n) ∧
        mX c n - ε β ≤ AX c n β / β ∧ AX c n β / β ≤ mX c n) ∧
      ∀ F : OverlapField c n,
        Integrable (fun ω => Real.log (∫ s, Real.exp (β * F.Y s ω) ∂(RGGDetect.prior n 3))) F.P ∧
        Integrable (fun ω => sSup (range fun s => F.Y s ω)) F.P ∧
        mY F - ε β ≤ AY F β / β ∧ AY F β / β ≤ mY F) ∧
    (∀ (F : ∀ n, OverlapField c n) (G : ℝ → ℝ),
      (∀ β : ℝ, 0 < β → Tendsto (fun n => AY (F n) β / β) atTop (𝓝 (G β))) →
      ∃ L : ℝ, Tendsto (mX c) atTop (𝓝 L) ∧ Tendsto (fun n => mY (F n)) atTop (𝓝 L) ∧
        Tendsto G atTop (𝓝 L)) := by sorry

end QPSpinParisi
