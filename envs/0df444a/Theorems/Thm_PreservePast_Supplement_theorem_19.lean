-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_19
-- name    : PreservePast.Supplement.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:42:44.273674+00:00
-- url     : https://prove2.me/theorems/1b5efa5d-8dda-40ba-af45-daa7acfae8e2
-- title:
--   Theorem 19 — near-Bayes prediction with vanishing raw-record recoverability
-- statement:
--   In the nearest-of-$k$ experiment on the cube, in the weak-signal window $\rho^2d=2\ln k+\tau\sqrt{\ln k}$, $|\tau|\le T_0$, $d\ge k^{0.1}$, let integers $r\to\infty$ with $r=o(\sqrt{\ln k})$, and partition the coordinates into $r$ public balanced nonempty blocks. There is a deterministic encoder and decoder with Bayes excess error $o(1)$ for which, for every record $j$,
--   $$H(X_j\mid M)=r=o(d),\qquad \sup_{\hat X_j}\Pr\{\hat X_j(M)=X_j\}\le 2^{-r},$$
--   where independent estimator randomization is allowed, and for every fixed $\eta>0$,
--   $$\Pr\{\operatorname{dist}_H(X_j,\hat X_j(M))\le(\tfrac12-\eta)d\}\le\exp\Big(-\frac{2\eta^2r}{1+r/d}\Big)=o(1).$$
--   The whole-dataset information is $k(d-r)=(1-o(1))kd$, and $kr=o(kd)$ additional helper bits recover it exactly. For $\rho^2d=2c\ln k$ with fixed $c>1$, the construction also has success $1-o(1)$ whenever $r=o(\ln k)$.
--
--   So a model can retain almost all the information in its training set while no individual record can be reconstructed from it.
--
--   **Formalization Note** $r$ is a sequence $r_k$; the record-hiding clauses are the predicate `HidesRecords`.
--
--   Differences from the source:
--   - encoding: o(1) as k → ∞ → a sequence e_k → 0 valid for all admissible (d, ρ, τ) at each k; reason: equivalent to the statement for every sequence of parameters
--   - encoding: partition the coordinates into r public balanced nonempty blocks → the hypothesis 1 ≤ r_k ≤ d, with no partition in the statement; reason: such a partition exists exactly when 1 ≤ r ≤ d, which holds for large k, and the conclusion does not mention the partition
--   - encoding: r = o(d), k(d − r) = (1 − o(1))kd, kr = o(kd), and exp(−2η²r/(1 + r/d)) = o(1) → the clauses r_k ≤ e_k·d and exp(−2η²r_k/(1 + r_k/d)) ≤ e_k with e_k → 0; reason: the three magnitude remarks are the single bound r_k/d → 0
--   - encoding: the construction also has success 1 − o(1) whenever r = o(ln k) → for r_k → ∞ with r_k = o(ln k), in the supercritical regime there is an encoder and decoder with success ≥ 1 − e_k and the same record-hiding properties; reason: "the construction" is identified by the properties (238)–(239) it was shown to have
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 19, p.65 (PDF p.67), eqs. (238)–(239); Definition 1, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_PreservePast_Supplement_HidesRecords

open MeasureTheory Filter Topology Asymptotics

namespace PreservePast.Supplement

/-- **Theorem 19 (Near-Bayes prediction with vanishing raw-record recoverability).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa),
Theorem 19, p.65 (PDF p.67), eqs. (238)–(239); the experiment is Definition 1, p.10.

In the weak-signal window `ρ²d = 2 ln k + τ√(ln k)`, `|τ| ≤ T₀`, `d ≥ k^{0.1}`, for integers
`r → ∞` with `r = o(√(ln k))` and `r` public balanced nonempty blocks of coordinates, there is a
deterministic encoder and decoder with Bayes excess error `o(1)` for which `H(X_j | M) = r = o(d)`,
no (randomized) estimator recovers `X_j` with probability above `2^{−r}`, for every fixed `η > 0`
`Pr{dist_H(X_j, X̂_j(M)) ≤ (1/2 − η)d} ≤ exp(−2η²r/(1 + r/d)) = o(1)`, the whole-dataset
information is `k(d − r) = (1 − o(1))kd`, and `kr = o(kd)` helper bits recover the database. For
`ρ²d = 2c ln k`, `c > 1` fixed, the construction also has success `1 − o(1)` whenever
`r = o(ln k)`.

**Formalization Note.** `r` is a sequence `r_k`; each `o(1)` is a sequence `e_k → 0` valid for
all admissible `(d, ρ, τ)` at each `k`. Balanced nonempty blocks exist exactly when
`1 ≤ r_k ≤ d`, which is assumed (it holds for large `k`); the conclusion does not mention the
partition, so it is stated once. The recoverability clauses are the predicate `HidesRecords`.
"`= o(d)`", "`(1 − o(1))kd`" and "`kr = o(kd)`" are the clause `r_k ≤ e_k d`; "`= o(1)`" in
(239) is the second conjunct. In the supercritical clause (`r_k → ∞`, `r_k = o(ln k)`) the
encoder has the same record-hiding properties and success `≥ 1 − e_k`. -/
theorem theorem_19 :
    (∀ (T₀ : ℝ) (r : ℕ → ℕ), Tendsto r atTop atTop →
        (fun k => (r k : ℝ)) =o[atTop] (fun k : ℕ => Real.sqrt (Real.log k)) →
        (∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
          ∀ (k d : ℕ) (ρ τ : ℝ), 2 ≤ k → (k : ℝ) ^ (0.1 : ℝ) ≤ d → 0 < ρ → ρ < 1 → |τ| ≤ T₀ →
            ρ ^ 2 * d = 2 * Real.log k + τ * Real.sqrt (Real.log k) → 1 ≤ r k → r k ≤ d →
            (r k : ℝ) ≤ e k * d ∧
            ∃ (N : ℕ) (enc : (Fin k → Fin d → Bool) → Fin N)
              (dec : Fin N → (Fin d → Bool) → Fin k),
              bayesSuccess k d ρ - e k ≤ detIdSuccess enc dec ρ ∧ HidesRecords (r k) enc) ∧
        ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
          ∀ k d : ℕ, 2 ≤ k → (k : ℝ) ^ (0.1 : ℝ) ≤ d → 1 ≤ r k → r k ≤ d →
            Real.exp (-2 * η ^ 2 * r k / (1 + r k / d)) ≤ e k) ∧
    ∀ (c : ℝ) (r : ℕ → ℕ), 1 < c → Tendsto r atTop atTop →
      (fun k => (r k : ℝ)) =o[atTop] (fun k : ℕ => Real.log k) →
      ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
        ∀ (k d : ℕ) (ρ : ℝ), 2 ≤ k → (k : ℝ) ^ (0.1 : ℝ) ≤ d → 0 < ρ → ρ < 1 →
          ρ ^ 2 * d = 2 * c * Real.log k → 1 ≤ r k → r k ≤ d →
          ∃ (N : ℕ) (enc : (Fin k → Fin d → Bool) → Fin N)
            (dec : Fin N → (Fin d → Bool) → Fin k),
            1 - e k ≤ detIdSuccess enc dec ρ ∧ HidesRecords (r k) enc := by sorry

end PreservePast.Supplement
