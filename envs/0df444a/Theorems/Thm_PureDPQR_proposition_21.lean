-- Prove2me | Theorems.Thm_PureDPQR_proposition_21
-- name    : PureDPQR.proposition_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:59:33.666175+00:00
-- url     : https://prove2.me/theorems/bc2b40ff-7db0-496f-b483-c9c03a5d0bd0
-- title:
--   Proposition 21, p.23 — accuracy of the unperturbed SelectMW$(h)$, bound (5.10)
-- statement:
--   **Proposition 21** (Accuracy of the unperturbed process). Let $Q=\{q_1,\dots,q_k\}\subset[0,1]^d$ ($k\ge1$), $K=2k$ with its signed list, $h\in H_{N,d}$, and run SelectMW$(h)$ (Algorithm 1 with $N,T\ge1$, $\lambda>0$, $0<\rho\le\frac12$) on the true histogram. For every $0<\theta<1$, with probability at least $1-\theta$ over the transcript $y\sim p_h$,
--
--   $$\mathrm{err}_Q(D(y),h)\le\frac{\log d}{\rho T}+\rho+\frac{\log K}{N\lambda}+4\sqrt{\frac{2\log(1/\theta)}{T}} .$$
--
--   It is the utility guarantee of the process that Algorithm 2 runs, on the event that no coordinate is perturbed.
--
--   **Formalization Note** The probability is $\sum p_h(y)$ over the transcripts $y\in[K]^T$ satisfying the bound; $\log K=\log(2k)$.
--
--   Differences from the source:
--   - reading: a workload Q = {q_1, …, q_k} → k ≥ 1; reason: with k = 0 the label set [K] is empty and Algorithm 1 cannot draw; Theorem 2 has k ≥ 1
--   - encoding: "with probability at least 1 − θ" → 1 − θ ≤ Σ of p_h(y) over the transcripts y satisfying (5.10); reason: p_h is a law on the finite set [K]^T; same probability
--   - encoding: 1-based signed list s_{2i−1} = q_i, s_{2i} = −q_i → 0-based signed Q (2i) = q_i, (2i+1) = −q_i; reason: Lean convention; same list
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Proposition 21, p.23 (PDF p.24); Algorithm 1, p.19; §5, p.18

import Mathlib
import Definitions.Def_PureDPQR_IsDP
import Definitions.Def_PureDPQR_errQ
import Definitions.Def_PureDPQR_transcriptProb

namespace PureDPQR

open Classical in
/-- **Proposition 21** (Accuracy of the unperturbed process), p.23 (PDF p.24).

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…).

"Run SelectMW(h) on the true histogram h. For every 0 < θ < 1, with probability at least 1 − θ,
errQ(D(y), h) ≤ log d/(ρT) + ρ + log K/(Nλ) + 4 √(2 log(1/θ)/T). (5.10)"

Setting (§5, p.18; Algorithm 1, p.19): a public workload `Q = {q_1, …, q_k}` with
`q_i ∈ [0,1]^d`, `K = 2k`, the signed list `s`, the true histogram `h ∈ H_{N,d}`, and
Algorithm 1's Require line `N, T ≥ 1`, `λ > 0`, `0 < ρ ≤ 1/2`.

**Formalization Note.** "With probability at least `1 − θ`" is the sum of `p_h(y)` over the
transcripts `y ∈ [K]^T` satisfying (5.10). `k ≥ 1` (so `[K]` is nonempty, as in Theorem 2) is
stated. `log K = log(2k)`; `λ` is written `lam`. -/
theorem proposition_21 {k d T : ℕ} (N : ℕ) (lam ρ : ℝ) (Q : Fin k → Fin d → ℝ) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hlam : 0 < lam) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 2)
    (hQ : ∀ i j, Q i j ∈ Set.Icc (0 : ℝ) 1) (h : Fin d → ℕ) (hh : h ∈ histograms N d)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    1 - θ ≤
      ∑ y ∈ (Finset.univ : Finset (Fin T → Fin (2 * k))).filter (fun y =>
          errQ N Q (decoder ρ (signed Q) y) h ≤
            Real.log d / (ρ * T) + ρ + Real.log (2 * (k : ℝ)) / (N * lam) +
              4 * Real.sqrt (2 * Real.log (1 / θ) / T)),
        transcriptProb N lam ρ (signed Q) (fun j => (h j : ℝ)) y := by sorry

end PureDPQR
