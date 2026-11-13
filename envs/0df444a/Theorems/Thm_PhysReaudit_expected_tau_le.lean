-- Prove2me | Theorems.Thm_PhysReaudit_expected_tau_le
-- name    : PhysReaudit.expected_tau_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:47:35.901425+00:00
-- url     : https://prove2.me/theorems/8b4210e3-0bce-4ca4-a0e6-454a0ee23f61
-- title:
--   Proof of Theorem 4, p.4 — $\mathbb E_q\tau\le(A+z_+)/D$ on the good class
-- statement:
--   Let $0<q_0<t<1$, $0<\delta<\tfrac12$, $A=\log(1/\delta)$, $D=\mathrm{kl}(q_0,t)$ and $z_+=\log((1-q_0)/(1-t))$. For every $q\in[0,q_0]$, the SPRT stopping index $\tau=\inf\{n\ge1:S_n\ge A\text{ or }S_n\le-A\}$ of i.i.d. Bernoulli$(q)$ target outcomes satisfies
--
--   $$
--   \mathbb E_q\tau\ \le\ \frac{A+z_+}{D},
--   $$
--
--   without any integrability assumption on $\tau$. Multiplied by the navigation multiplier, this is the upper bound of Theorem 4.
--
--   **Formalization Note** $\mathbb E_q\tau$ is an expectation in $[0,\infty]$ of the $\mathbb N\cup\{\infty\}$-valued $\tau$.
--
--   Differences from the source:
--   - encoding: q₀ = (b − ε)/(κp), t = b/(κp) with 0 < ε < b < κp → any reals 0 < q₀ < t < 1; reason: exactly the pairs that arise (κ = a = 1, b = t, ε = t − q₀ realise any such pair), so the same instances
--   - encoding: the SPRT's target observations Y_1, Y_2, … and F_n = σ(Y_1, …, Y_n) → the coordinates y 0, y 1, … of the i.i.d. Bernoulli(q) target tape (Measure.infinitePi of bern q) and pastFiltration n (coordinates < n); reason: the SPRT reads the target tape in order, so its i-th observation is target entry i − 1
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5), "Monotone convergence proves Eqτ ≤ (A + z+)/D, without presupposing integrability of τ."

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_lawQ
import Definitions.Def_PhysReaudit_sprtS

open MeasureTheory
open LimitedPriceChanges.LowerBound (klBer)

namespace PhysReaudit

/-- **Expected stopping index on the good class** (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)): "Monotone
convergence proves Eqτ ≤ (A + z+)/D, without presupposing integrability of τ."

For `0 < q₀ < t < 1`, `0 < δ < 1/2`, `A = log(1/δ)`, `D = kl(q₀, t)` and every `q ∈ [0, q₀]`, the SPRT stopping
index `τ` on the i.i.d. Bernoulli(q) target tape satisfies `E_q τ ≤ (A + z₊)/D` (in `ℝ≥0∞`; no integrability
is assumed). -/
theorem expected_tau_le {q₀ t δ : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) (hδ : 0 < δ)
    (hδ1 : δ < 1 / 2) {q : ℝ} (hq : q ∈ Set.Icc 0 q₀) :
    ∫⁻ y, (sprtTau q₀ t δ y : ENNReal) ∂(Measure.infinitePi fun _ : ℕ => bern q)
      ≤ ENNReal.ofReal ((Real.log (1 / δ) + zPlus q₀ t) / klBer q₀ t) := by sorry

end PhysReaudit
