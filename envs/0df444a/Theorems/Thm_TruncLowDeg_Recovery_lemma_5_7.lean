-- Prove2me | Theorems.Thm_TruncLowDeg_Recovery_lemma_5_7
-- name    : TruncLowDeg.Recovery.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:24:26.715882+00:00
-- url     : https://prove2.me/theorems/40fc1008-6d19-469b-800d-77de0e73048c
-- title:
--   Lemma 5.7 — polynomial norms on the cube and uniform concentration of empirical averages (with $d^{O(k)}$ read as $d^{Ck}$)
-- statement:
--   Let $k\ge1$, $\rho\ge1$ and $U=\mathrm{Unif}([-\rho,\rho]^d)$. For $p\in\mathbb R[x]_{\le k}$, $a\in\mathbb R[x]$ and $j\in\{1,\dots,d\}$,
--   $$\sup_{y\in[-\rho,\rho]^d}|p(y)|\le d^{O(k)}\|p\|_{L^2(U)},\quad \|pa\|_{L^2(U)}\le d^{O(k)}\|p\|_{L^2(U)}\|a\|_{L^2(U)},\quad \|\partial_jp\|_{L^2(U)}\le d^{O(k)}\|p\|_{L^2(U)} .$$
--   Moreover, if $Q$ is a probability distribution supported on $[-\rho,\rho]^d$, $\eta>0$, $\delta'\in(0,1)$ and $X_1,\dots,X_m$ are independent samples from $Q$ with $m\ge d^{O(k)}/(\delta'\eta^2)$, then with probability at least $1-\delta'$
--   $$\Big|\frac1m\sum_{i=1}^mf(X_i)-\mathbb E_{X\sim Q}[f(X)]\Big|\le\eta\,\|f\|_{L^2(U)}\qquad\forall f\in\mathbb R[x]_{\le k}.$$
--   These are the norm comparisons and the uniform concentration used to establish (15) and to analyse system (14).
--
--   **Formalization Note.** $d^{O(k)}$ is read literally as $d^{Ck}$ with one universal $C$. At $d=1$ this reading makes the bounds $k$-independent constants, and the norm bounds are then false (finding I1: $p(x)=x$ on $[-1,1]$); the statement is posed as printed.
--
--   Differences from the source:
--
--   - reading: d^{O(k)} (three norm bounds and the sample bound) → d^{C·k} with one universal constant C fixed before d, k, ρ, p, a, Q, η, δ′, m; reason: the literal and stronger reading of the paper's convention; it fails at d = 1 (finding I1) and is kept as printed
--   - reading: ℝ^d with the dimension left implicit → hypothesis `1 ≤ d`; reason: the paper works in ℝ^d with d ≥ 1 (coordinates j ∈ {1, …, d}); at d = 0 the expressions d^{O(k)}, (d + L²) and d·t^{1/k} degenerate and the paper never considers it
--   - encoding: ℝ^d, coordinates j ∈ {1, …, d} → `Vec d = EuclideanSpace ℝ (Fin d)`, 0-based coordinates `Fin d`; reason: Lean convention; same instances
--   - encoding: Q a probability distribution supported on [−ρ, ρ]^d → a probability measure Q on the Borel sets of ℝ^d with Q((cube)ᶜ) = 0; reason: a law supported on a closed set gives its complement measure 0
--   - encoding: with probability at least 1 − δ′, the bound for all f ∈ ℝ[x]_{≤k} → the product measure of the set of samples on which the bound fails for some f of total degree ≤ k is at most δ′; reason: one event for all f simultaneously; a failure-set bound avoids an outer-measure reading
-- source:
--   Vári-Kakas, Wiedmer, A General Approach to Polynomial-Time Truncated Learning via Low-Degree Moments, STOC 2027 submission (manuscript sha256 613f0e39…), p. 24, Lemma 5.7; proof pp. 24–25

import Definitions.Def_TruncLowDeg_Recovery_Basic

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace TruncLowDeg.Recovery

/-- Lemma 5.7 (p. 24): polynomial norms on the cube and uniform concentration. One universal
constant `C`, with `d^{O(k)}` read literally as `d^{C k}`: for `d ≥ 1`, `k ≥ 1`, `ρ ≥ 1` and
`U = Unif([−ρ, ρ]^d)`, every `p ∈ ℝ[x]_{≤k}`, every polynomial `a` and every coordinate `j`
satisfy `sup_{[−ρ,ρ]^d} |p| ≤ d^{Ck} ‖p‖_{L²(U)}`, `‖pa‖_{L²(U)} ≤ d^{Ck} ‖p‖_{L²(U)} ‖a‖_{L²(U)}`
and `‖∂_j p‖_{L²(U)} ≤ d^{Ck} ‖p‖_{L²(U)}`; and for every probability measure `Q` carried by the
cube, `η > 0`, `δ' ∈ (0, 1)` and `m ≥ d^{Ck}/(δ'η²)`, with probability at least `1 − δ'` over
`m` independent samples from `Q`, `|(1/m) ∑ f(X_i) − E_Q f| ≤ η ‖f‖_{L²(U)}` for all
`f ∈ ℝ[x]_{≤k}` simultaneously (the failure set has measure at most `δ'`). -/
theorem lemma_5_7 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k : ℕ) (ρ : ℝ), 1 ≤ d → 1 ≤ k → 1 ≤ ρ →
        (∀ p a : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ k → ∀ j : Fin d,
          supAbs p (cube d ρ) ≤ (d : ℝ) ^ (C * k) * L2U ρ p ∧
          L2U ρ (p * a) ≤ (d : ℝ) ^ (C * k) * L2U ρ p * L2U ρ a ∧
          L2U ρ (MvPolynomial.pderiv j p) ≤ (d : ℝ) ^ (C * k) * L2U ρ p) ∧
        (∀ Q : Measure (Vec d), IsProbabilityMeasure Q → Q (cube d ρ)ᶜ = 0 →
          ∀ η δ' : ℝ, 0 < η → 0 < δ' → δ' < 1 →
          ∀ m : ℕ, (d : ℝ) ^ (C * k) / (δ' * η ^ 2) ≤ m →
            (Measure.pi fun _ : Fin m => Q)
              {X | ¬ ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ k →
                |(1 / (m : ℝ)) * ∑ i, peval f (X i) - ∫ x, peval f x ∂Q| ≤ η * L2U ρ f} ≤
              ENNReal.ofReal δ') := by sorry

end TruncLowDeg.Recovery
