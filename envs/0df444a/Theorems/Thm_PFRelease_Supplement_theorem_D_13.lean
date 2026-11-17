-- Prove2me | Theorems.Thm_PFRelease_Supplement_theorem_D_13
-- name    : PFRelease.Supplement.theorem_D_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:47:03.108921+00:00
-- url     : https://prove2.me/theorems/fe6c78c9-3cb9-4d1c-97e7-2136e1c8320c
-- title:
--   Theorem D.13 — private subspace estimation on the geometric spectrum retains every record and gives $\|\widetilde P-P_k(\Sigma)\|\le\alpha$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $d,k,n,b\in\mathbb N$ with $n/b\in\mathbb N$, $d\ge8$ and $\lceil\log_2 d\rceil<k\le d/2$; let $\alpha\in(0,1/4]$, $\beta\in(0,1/4)$, $\varepsilon\in(0,1]$, $\delta\in(0,2\beta]$; and let $\Sigma$ be a covariance with the geometric spectrum (arbitrary eigenvectors). Put
--   $$
--   L:=\ln(16/\delta),\quad \lambda:=\frac{2^{-\lceil\log_2 d\rceil}}{d},\quad r:=\Big\lceil\frac{C(k+\ln(1/\beta))}{\alpha^2}\Big\rceil,\quad \tau:=\frac1{C(k+\ln(n/\beta))}.
--   $$
--   Suppose
--   $$
--   b\ge C\big(k+\ln(n/\beta)\big),\qquad \frac nb\ge\max\Big\{\frac{400L^2}{\varepsilon^{3/2}},\ \frac{1800L\ln(8n/\beta)}{\varepsilon^{3/2}}\Big\},\qquad n\ge\frac{C(k+\ln(1/\beta))}{\alpha^2},
--   $$
--   and that the records $X_1,\dots,X_n$ are independent draws from $\mathcal N(0,\Sigma)$. Then, with probability at least $1-\beta$ (over the records, the filter's partition and noises, and the sketches), the subspace mechanism with parameters $\lambda,r,\tau$ retains every record in its filter and returns $\widetilde P$ with
--   $$
--   \|\widetilde P-P_k(\Sigma)\|\le\alpha,
--   $$
--   where $\|\cdot\|$ is the operator norm and $P_k(\Sigma)$ is the projector onto the top $k$ eigenvectors of $\Sigma$.
--
--   The subspace mechanism runs $\mathrm{PFR}_b^{\varepsilon,\delta}(M_{\lambda,r},\varphi_\lambda,\tau)$ (the filter of Theorem 4.5, with $t=7n/(8b)$, $\sigma_F=12/\varepsilon$, $\sigma_F'=108L/\varepsilon^{3/2}$, $\kappa=2\sigma_FL$, testing $F_{2\tau}(\varphi_\lambda)$, followed by the Gaussian sketches) and returns the projector $\widetilde P$ onto the top $k$ eigenvectors of $R=r^{-1}\sum_jZ_jZ_j^T$. The number of records needed does not grow with $d$ for a fixed rank.
--
--   **Formalization Note** The constant $C$ is chosen before every other quantity. A covariance with the geometric spectrum is $U\,\mathrm{diag}(\lambda_1,\dots,\lambda_d)\,U^T$ for an arbitrary orthogonal $U$. The input has no null records, so "retains every record" means the filter nulls the empty set; on that event the release runs on the data itself. Given the data, the probability of "nothing nulled and the output is good" is therefore the probability that the filter nulls nothing times the probability that the sketches are good, and its expectation over $\mathcal N(0,\Sigma)^{\otimes n}$ is bounded below. "Good" requires $\|\widetilde P-Q\|\le\alpha$ for every top-$k$ eigenprojector $\widetilde P$ of $R$ and every top-$k$ eigenprojector $Q$ of $\Sigma$ (unique, since $\lambda_k(\Sigma)=2\lambda_{k+1}(\Sigma)$).
--
--   Differences from the source:
--   - reading: P̃, the projector onto the top k eigenvectors of R (not unique when λ_k(R) = λ_{k+1}(R)) → every top-k eigenprojector P of R satisfies the bound; reason: the source does not fix a tie-breaking rule; requiring the bound for every top-k eigenprojector implies it for every rule
--   - encoding: P_k(Σ) → every top-k eigenprojector Q of Σ; reason: P_k(Σ) is unique on the geometric spectrum (λ_k = 2λ_{k+1}), so this is the same object
--   - encoding: there exists a universal constant C → ∃ C : ℝ, 0 < C, chosen before d, k, n, b, α, β, ε, δ and Σ; reason: the theorem's own quantifier; requiring C > 0 only strengthens it
--   - encoding: a covariance Σ with the geometric spectrum and arbitrary unknown eigenvectors → Σ = U diag(geomSpectrum d k) Uᵀ for every orthogonal U; reason: the symmetric matrices with this spectrum
--   - encoding: with probability at least 1 − β, the filter retains every record and returns P̃ with ‖P̃ − P_k(Σ)‖ ≤ α → the lower integral over N(0, Σ)^{⊗n} of filterLaw … s ∅ · M_{λ,r}(s){good} is at least 1 − β; reason: with no null records, retaining every record is I = ∅, on which the PFR release runs on s; this is the probability of the joint event
--   - encoding: ⌈log₂ d⌉, r = ⌈·⌉, records in ℝ^d, N(0, A) → Nat.clog 2 d, Nat.ceil, EuclideanSpace ℝ (Fin d), multivariateGaussian 0 A; reason: Lean conventions, same values and laws
--   - encoding: n/b ∈ ℕ → hypotheses 0 < b and b ∣ n; reason: same instances
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.13, p.45 (PDF p.47); subspace mechanism and geometric spectrum, §5.2, pp.17–18 (PDF pp.19–20); Definition D.7, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_PFRelease_IsScore
import Definitions.Def_PFRelease_filterLaw
import Definitions.Def_PFRelease_Supplement_phiLam
import Definitions.Def_PFRelease_Supplement_sketchMech

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix.Norms.L2Operator

namespace PFRelease.Supplement

/-- **Theorem D.13 (Subspace estimation on the geometric spectrum)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private
Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Theorem D.13,
p.45 = PDF p.47; informal version Theorem 5.3, p.18). There exists a universal constant `C` such that
the following holds. Given `d, k, n, b ∈ ℕ` with `n/b ∈ ℕ`, `d ≥ 8` and `⌈log₂ d⌉ < k ≤ d/2`;
`α ∈ (0, 1/4]`; `β ∈ (0, 1/4)`; `ε ∈ (0, 1]`; `δ ∈ (0, 2β]`; and a covariance `Σ` with the geometric
spectrum, if `b ≥ C(k + ln(n/β))`, `n/b ≥ max{400L²/ε^{3/2}, 1800L ln(8n/β)/ε^{3/2}}`,
`n ≥ C(k + ln(1/β))/α²` and the records are independent draws from `N(0, Σ)`, then with probability at
least `1 − β` the subspace mechanism with parameters `λ, r, τ` retains every record in its filter and
returns `P̃` with `‖P̃ − P_k(Σ)‖ ≤ α`, where `L := ln(16/δ)`, `λ := 2^{−⌈log₂ d⌉}/d`,
`r := ⌈C(k + ln(1/β))/α²⌉` and `τ := 1/(C(k + ln(n/β)))`.

**Formalization Note**
* `∃ C > 0` is chosen before every other quantity. Records are vectors of `EuclideanSpace ℝ (Fin d)`,
  all non-null (`some`). A covariance with the geometric spectrum (arbitrary eigenvectors) is
  `Σ = U diag(geomSpectrum d k) Uᵀ` for an arbitrary orthogonal `U`. `⌈log₂ d⌉` is `Nat.clog 2 d`,
  and `r` is the natural-number ceiling.
* The subspace mechanism runs `PFR_b^{ε,δ}(M_{λ,r}, φ_λ, τ)` (the filter of Theorem 4.5 with
  `t = 7n/(8b)`, `σ_F = 12/ε`, `σ_F′ = 108L/ε^{3/2}`, `κ = 2σ_F L`, testing `F_{2τ}(φ_λ)`), then returns
  the projector onto the top `k` eigenvectors of `R = r⁻¹ Σ_j Z_j Z_jᵀ`. The input has no null records,
  so "retains every record" is the filter's nulled set `I = ∅`, on which the release runs on the data
  itself. The probability of "`I = ∅` and the output is good" given the data is therefore
  `filterLaw … s ∅ · M_{λ,r}(s){good}`, and its expectation over `N(0, Σ)^{⊗n}` (a lower Lebesgue
  integral) is bounded below.
* "Good" holds for **every** projector `P̃` onto a top-`k` eigenspan of `R` (ties broken arbitrarily) and
  every top-`k` eigenprojector `Q` of `Σ` (unique here, since `λ_k(Σ) = 2λ_{k+1}(Σ)`); `‖·‖` is the
  operator (spectral) norm. -/
theorem theorem_D_13 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k n b : ℕ), 0 < b → b ∣ n → 8 ≤ d → Nat.clog 2 d < k → 2 * k ≤ d →
      ∀ (α β ε δ : ℝ), 0 < α → α ≤ 1 / 4 → 0 < β → β < 1 / 4 → 0 < ε → ε ≤ 1 →
        0 < δ → δ ≤ 2 * β →
      ∀ U : Matrix (Fin d) (Fin d) ℝ, U ∈ Matrix.orthogonalGroup (Fin d) ℝ →
        let L := Real.log (16 / δ)
        let Sig : Matrix (Fin d) (Fin d) ℝ := U * diagonal (geomSpectrum d k) * Uᵀ
        let lam : ℝ := (2 : ℝ)⁻¹ ^ Nat.clog 2 d / d
        let r : ℕ := ⌈C * (k + Real.log (1 / β)) / α ^ 2⌉₊
        let τ : ℝ := 1 / (C * (k + Real.log (n / β)))
        let t := 7 * (n : ℝ) / (8 * (b : ℝ))
        let σF := 12 / ε
        let σF' := 108 * L / ε ^ (3 / 2 : ℝ)
        let κ := 2 * σF * L
        C * (k + Real.log (n / β)) ≤ b →
        max (400 * L ^ 2 / ε ^ (3 / 2 : ℝ)) (1800 * L * Real.log (8 * n / β) / ε ^ (3 / 2 : ℝ))
          ≤ (n : ℝ) / b →
        C * (k + Real.log (1 / β)) / α ^ 2 ≤ n →
        ENNReal.ofReal (1 - β) ≤
          ∫⁻ Xs : Fin n → EuclideanSpace ℝ (Fin d),
            filterLaw b t κ σF σF' (predOf (phiLam lam) (2 * τ)) (fun i => some (Xs i)) ∅ *
              sketchMech lam r (fun i => some (Xs i))
                {Z | ∀ P Q : Matrix (Fin d) (Fin d) ℝ, IsTopKProj (sketchCov Z) k P →
                  IsTopKProj Sig k Q → ‖P - Q‖ ≤ α}
            ∂(Measure.pi fun _ : Fin n => multivariateGaussian 0 Sig) := by sorry

end PFRelease.Supplement
