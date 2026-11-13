-- Prove2me | Theorems.Thm_PhysReaudit_multiplier_ge_t
-- name    : PhysReaudit.multiplier_ge_t
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:29.680635+00:00
-- url     : https://prove2.me/theorems/0037a686-cf0d-4e65-bf3a-3cdee4dd6727
-- title:
--   Proof of Theorem 4, p.4 — for $q\ge t$, $\mathbb E_q[e^{S_{n+1}-S_n}\mid\mathcal F_n]=1+\frac{(q-t)(q_0-t)}{t(1-t)}\le1$
-- statement:
--   Let $0<q_0<t<1$ and $q\in[t,1]$, and let $Y_1,Y_2,\dots$ be i.i.d. Bernoulli$(q)$ with $S_n=\sum_{i\le n}\{Y_iz_-+(1-Y_i)z_+\}$ and $\mathcal F_n=\sigma(Y_1,\dots,Y_n)$. Then for every $n\ge0$, almost surely,
--
--   $$
--   \mathbb E_q\big[e^{S_{n+1}-S_n}\mid\mathcal F_n\big]=1+\frac{(q-t)(q_0-t)}{t(1-t)}\ \le\ 1 .
--   $$
--
--   So $e^{S_n}$ has multipliers at most one under every harmful parameter, which is what makes Ville's inequality bound false acceptance of the SPRT.
--
--   Differences from the source:
--   - encoding: q₀ = (b − ε)/(κp), t = b/(κp) with 0 < ε < b < κp → any reals 0 < q₀ < t < 1; reason: exactly the pairs that arise (κ = a = 1, b = t, ε = t − q₀ realise any such pair), so the same instances
--   - encoding: the SPRT's target observations Y_1, Y_2, … and F_n = σ(Y_1, …, Y_n) → the coordinates y 0, y 1, … of the i.i.d. Bernoulli(q) target tape (Measure.infinitePi of bern q) and pastFiltration n (coordinates < n); reason: the SPRT reads the target tape in order, so its i-th observation is target entry i − 1
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5), display "Eq[e^{Sn+1−Sn} | Fn] = 1 + (q − t)(q0 − t)/(t(1 − t)) ≤ 1"

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory

namespace PhysReaudit

/-- **The likelihood-ratio multiplier for `q ≥ t`** (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5), display
"Eq[e^{Sn+1−Sn} | Fn] = 1 + (q − t)(q0 − t)/(t(1 − t)) ≤ 1").

Let `0 < q₀ < t < 1` and `q ∈ [t, 1]`. Under the i.i.d. Bernoulli(q) target tape, for every `n`,
the conditional expectation of `e^{S_{n+1} − S_n}` given `F_n = σ(Y_1, …, Y_n)` is almost surely the constant
`1 + (q − t)(q₀ − t)/(t(1 − t))`, and this constant is at most `1`. -/
theorem multiplier_ge_t {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) {q : ℝ}
    (hq : q ∈ Set.Icc t 1) (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => bern q)[fun y => Real.exp (sprtS q₀ t y (n + 1) - sprtS q₀ t y n)
        | pastFiltration n]
      =ᵐ[Measure.infinitePi fun _ : ℕ => bern q] (fun _ => 1 + (q - t) * (q₀ - t) / (t * (1 - t))) ∧
    1 + (q - t) * (q₀ - t) / (t * (1 - t)) ≤ 1 := by sorry

end PhysReaudit
