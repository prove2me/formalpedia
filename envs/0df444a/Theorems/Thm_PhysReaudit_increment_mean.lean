-- Prove2me | Theorems.Thm_PhysReaudit_increment_mean
-- name    : PhysReaudit.increment_mean
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:17.006032+00:00
-- url     : https://prove2.me/theorems/d5e3abc9-3692-44ec-8df2-a0079bef43da
-- title:
--   Proof of Theorem 4, p.4 — the increment mean $m(q)=qz_-+(1-q)z_+$ is decreasing, $m(q_0)=D>0$
-- statement:
--   Let $0<q_0<t<1$, $z_-=\log(q_0/t)$, $z_+=\log((1-q_0)/(1-t))$ and $D=\mathrm{kl}(q_0,t)$. The increment mean
--
--   $$
--   m(q)=q\,z_-+(1-q)\,z_+
--   $$
--
--   is strictly decreasing in $q$, satisfies $m(q)\ge m(q_0)$ for every $q\le q_0$, and
--
--   $$
--   m(q_0)=D>0 .
--   $$
--
--   So the SPRT statistic drifts upward at rate at least $D$ on the whole good class $q\le q_0$, which drives the bound on $\mathbb E_q\tau$.
--
--   **Formalization Note** $m$ is stated on all of $\mathbb R$; kl is the published binary relative entropy `klBer`.
--
--   Differences from the source:
--   - encoding: q₀ = (b − ε)/(κp), t = b/(κp) with 0 < ε < b < κp → any reals 0 < q₀ < t < 1; reason: exactly the pairs that arise (κ = a = 1, b = t, ε = t − q₀ realise any such pair), so the same instances
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), proof of Theorem 4, p.4 (PDF p.5), "The increment mean m(q) = qz− + (1 − q)z+ is decreasing in q and satisfies m(q) ≥ m(q0) = D > 0 on the good class."

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_KL
import Definitions.Def_PhysReaudit_Delta

open LimitedPriceChanges.LowerBound (klBer)

namespace PhysReaudit

/-- **The increment mean** (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), proof of Theorem 4, p.4 (PDF p.5)): "The increment mean
m(q) = qz− + (1 − q)z+ is decreasing in q and satisfies m(q) ≥ m(q0) = D > 0 on the good class."

For `0 < q₀ < t < 1`, the map `m(q) = q z₋ + (1 − q) z₊` is strictly decreasing on `ℝ`, `m(q₀) = kl(q₀, t)`,
and `kl(q₀, t) > 0`; hence `m(q) ≥ m(q₀) = D > 0` for every `q ≤ q₀`. -/
theorem increment_mean {q₀ t : ℝ} (h0 : 0 < q₀) (h1 : q₀ < t) (h2 : t < 1) :
    StrictAnti (fun q : ℝ => q * zMinus q₀ t + (1 - q) * zPlus q₀ t) ∧
    (∀ q ≤ q₀, q₀ * zMinus q₀ t + (1 - q₀) * zPlus q₀ t ≤ q * zMinus q₀ t + (1 - q) * zPlus q₀ t) ∧
    q₀ * zMinus q₀ t + (1 - q₀) * zPlus q₀ t = klBer q₀ t ∧
    0 < klBer q₀ t := by sorry

end PhysReaudit
