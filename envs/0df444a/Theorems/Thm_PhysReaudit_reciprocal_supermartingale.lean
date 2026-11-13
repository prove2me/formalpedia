-- Prove2me | Theorems.Thm_PhysReaudit_reciprocal_supermartingale
-- name    : PhysReaudit.reciprocal_supermartingale
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:12.101946+00:00
-- url     : https://prove2.me/theorems/03280286-3dd5-41a0-a7a0-8094ea577f82
-- title:
--   Proof of Theorem 4, p.4 — for $q\le q_0$, $e^{-S_n}$ is a nonnegative supermartingale
-- statement:
--   Let $0<q_0<t<1$ and $q\in[0,q_0]$, and let $Y_1,Y_2,\dots$ be i.i.d. Bernoulli$(q)$ with $S_n=\sum_{i\le n}\{Y_iz_-+(1-Y_i)z_+\}$ and $\mathcal F_n=\sigma(Y_1,\dots,Y_n)$. Then the expected multiplier of $e^{-S_n}$ satisfies
--
--   $$
--   q\,\frac{t}{q_0}+(1-q)\,\frac{1-t}{1-q_0}\ \le\ 1,
--   $$
--
--   and $(e^{-S_n})_{n\ge0}$ is a nonnegative supermartingale with respect to $(\mathcal F_n)$. This is the step that bounds the SPRT's lower-boundary probability on the good class.
--
--   Differences from the source:
--   - encoding: q₀ = (b − ε)/(κp), t = b/(κp) with 0 < ε < b < κp → any reals 0 < q₀ < t < 1; reason: exactly the pairs that arise (κ = a = 1, b = t, ε = t − q₀ realise any such pair), so the same instances
--   - encoding: the SPRT's target observations Y_1, Y_2, … and F_n = σ(Y_1, …, Y_n) → the coordinates y 0, y 1, … of the i.i.d. Bernoulli(q) target tape (Measure.infinitePi of bern q) and pastFiltration n (coordinates < n); reason: the SPRT reads the target tape in order, so its i-th observation is target entry i − 1
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5), "For every q ≤ q0, the reciprocal e−Sn is a nonnegative supermartingale, because its expected multiplier is q t/q0 + (1 − q)(1 − t)/(1 − q0) ≤ 1."

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory

namespace PhysReaudit

/-- **The reciprocal supermartingale for `q ≤ q₀`** (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)): "For every
q ≤ q0, the reciprocal e−Sn is a nonnegative supermartingale, because its expected multiplier is
q t/q0 + (1 − q)(1 − t)/(1 − q0) ≤ 1."

Let `0 < q₀ < t < 1` and `q ∈ [0, q₀]`. Then `q t/q₀ + (1 − q)(1 − t)/(1 − q₀) ≤ 1`, and under the i.i.d.
Bernoulli(q) target tape the process `e^{−S_n}` is nonnegative and a supermartingale for the filtration
`F_n = σ(Y_1, …, Y_n)`. -/
theorem reciprocal_supermartingale {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) {q : ℝ}
    (hq : q ∈ Set.Icc 0 q₀) :
    q * (t / q₀) + (1 - q) * ((1 - t) / (1 - q₀)) ≤ 1 ∧
    (∀ n y, 0 ≤ Real.exp (-sprtS q₀ t y n)) ∧
    Supermartingale (fun n y => Real.exp (-sprtS q₀ t y n)) pastFiltration
      (Measure.infinitePi fun _ : ℕ => bern q) := by sorry

end PhysReaudit
