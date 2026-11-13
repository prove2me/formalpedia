-- Prove2me | Theorems.Thm_PhysReaudit_expected_tau_finite
-- name    : PhysReaudit.expected_tau_finite
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:09.691468+00:00
-- url     : https://prove2.me/theorems/87dac5e4-4207-477c-896f-c3972d7be39e
-- title:
--   Proof of Theorem 4, p.4 — the SPRT terminates with finite expectation for every $q$
-- statement:
--   Let $0<q_0<t<1$ and $0<\delta<\tfrac12$. For every target parameter $q\in[0,1]$, including the unique zero-drift parameter in $(q_0,t)$ and the parameters in $(q_0,t]$ where neither output is required, the SPRT stopping index $\tau$ of i.i.d. Bernoulli$(q)$ target outcomes has
--
--   $$
--   \mathbb E_q\tau<\infty .
--   $$
--
--   In particular the SPRT terminates almost surely under every parameter.
--
--   Differences from the source:
--   - encoding: q₀ = (b − ε)/(κp), t = b/(κp) with 0 < ε < b < κp → any reals 0 < q₀ < t < 1; reason: exactly the pairs that arise (κ = a = 1, b = t, ε = t − q₀ realise any such pair), so the same instances
--   - encoding: the SPRT's target observations Y_1, Y_2, … and F_n = σ(Y_1, …, Y_n) → the coordinates y 0, y 1, … of the i.i.d. Bernoulli(q) target tape (Measure.infinitePi of bern q) and pastFiltration n (coordinates < n); reason: the SPRT reads the target tape in order, so its i-th observation is target entry i − 1
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5), "Thus termination has finite expectation for every q."

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory

namespace PhysReaudit

/-- **Finite expected termination for every parameter** (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)): "Thus
termination has finite expectation for every q."

For `0 < q₀ < t < 1` and `0 < δ < 1/2`, the SPRT stopping index `τ` on the i.i.d. Bernoulli(q) target tape has
`E_q τ < ∞` for every `q ∈ [0, 1]`, including the zero-drift parameter in `(q₀, t)`. -/
theorem expected_tau_finite {q₀ t δ : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∫⁻ y, (sprtTau q₀ t δ y : ENNReal) ∂(Measure.infinitePi fun _ : ℕ => bern q) < ⊤ := by sorry

end PhysReaudit
