-- Prove2me | Theorems.Thm_PersistQMem_eq_66_finite_records
-- name    : PersistQMem.eq_66_finite_records
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:37:48.363781+00:00
-- url     : https://prove2.me/theorems/a1401096-7832-4718-931f-9a856db2fa27
-- title:
--   §6.5, (66) — Theorem 2.2 for finite records: $N\ge4(1-\theta)[2s(\alpha-1)-1]/(\alpha^2\theta^2B_K)$ for every $\alpha>1$
-- statement:
--   Fix the data of Definition 2.1, an integer $K\ge1$, $0<\theta<1$ and $0\le\delta<1/2$, and put $s=1-2\delta$. Consider a persistent-memory receiver with a finite record alphabet (§5.4: a finite tree of classical histories), memory of dimension at most $K$ and at most $N$ copies. If a single decoder event $E$ satisfies (5),
--   $$\Pr_\tau(E)\le\delta,\qquad\sum_j\frac{p_j}2\sum_{z=\pm1}\Pr_{\rho_{j,z}}(E)\ge1-\delta,$$
--   then for every $\alpha>1$
--   $$N\ge\frac{4(1-\theta)[2s(\alpha-1)-1]}{\alpha^2\theta^2B_K}.\tag{66}$$
--
--   At $\alpha=2+1/s$ this is the bound (6) of Theorem 2.2; the paper first proves the theorem in this finite case.
--
--   Differences from the source:
--   - encoding: finite measurement alphabets (a finite tree of histories) → a Fintype record space with measurable singletons and counting reference measure in every round; reason: the finite tree of §5.4 with the refined Kraus index (p.19) is exactly this case
--   - encoding: receiver with retained dimension ≤ K on every branch, at most N copies, measurable instruments and controls on product σ-algebras of histories, terminal effects Q_h → Protocol X L K D (memory Fin K, rounds 0,…,N−1 of a round sequence, s-finite reference kernels on Fin t → X with jointly measurable Kraus densities complete for every history) and DecoderEvent X K N (entrywise measurable effect field); Pr_ρ(E) = prob P E ρ = ∫ Re Tr(Q_h ω^ρ_N(h)) dν_N; reason: registers of dimension ≤ K embed in C^K and early stopping is idling (pp.15, 28); per-round record spaces embed in one disjoint union; every measurable adaptive instrument has such a density (§6.6, (67)–(74)) and completeness off a ν-null set changes no probability
--   - encoding: z ∈ {−1, 1} → z : Bool with zsign true = 1, zsign false = −1; reason: Lean convention; same two signs
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), §6.5, (64)–(66), pp.25–27 (PDF pp.28–30)

import Mathlib
import Definitions.Def_PersistQMem_ProfileData
import Definitions.Def_PersistQMem_Protocol

open scoped Matrix ComplexOrder
open MeasureTheory

namespace PersistQMem

/-- **§6.5, (66), pp.25–27: Theorem 2.2 for finite records, for every `α > 1`** (Tao, Shen,
*Structural Lower Bounds for Quantum Property Estimation with Persistent Memory*, STOC 2027
submission, manuscript of 2026-11-03, sha256 6d48ad24…, §6.5, (66), p.27). Fix the data of
Definition 2.1, `K ≥ 1`, `0 < θ < 1`, `0 ≤ δ < 1/2`, `s = 1 − 2δ`, and a receiver with a finite
record alphabet (§5.4: a finite tree of classical histories). If a single decoder event `E` at
depth `N` satisfies (5), then for every `α > 1`
`N ≥ 4(1 − θ)[2s(α − 1) − 1] / (α²θ²B_K)`.

**Formalization Note.** Finite records are a `Fintype` record space with counting reference
measure in every round. -/
theorem eq_66_finite_records {D M : ℕ} {G : Fin M → Matrix (Fin D) (Fin D) ℂ} {p : Fin M → ℝ}
    (hG : ProfileData G p) (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1 / 2) (N : ℕ) (X : Type) [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (L : Type) [Fintype L]
    (P : Protocol X L K D) (hcount : ∀ t h, P.μ t h = Measure.count) (E : DecoderEvent X K N)
    (h5τ : prob P E (tau D) ≤ δ)
    (h5ρ : 1 - δ ≤ ∑ j, p j / 2 * ∑ z : Bool, prob P E (rhoAlt θ (G j) z))
    (α : ℝ) (hα : 1 < α) :
    4 * (1 - θ) * (2 * (1 - 2 * δ) * (α - 1) - 1) / (α ^ 2 * θ ^ 2 * budget G p K) ≤ N := by sorry

end PersistQMem
