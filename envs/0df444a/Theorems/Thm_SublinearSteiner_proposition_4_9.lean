-- Prove2me | Theorems.Thm_SublinearSteiner_proposition_4_9
-- name    : SublinearSteiner.proposition_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:47:57.020297+00:00
-- url     : https://prove2.me/theorems/1e483e55-ef5b-4035-9351-c82cde36c0ee
-- title:
--   Proposition 4.9 — the guarantee of the estimate
-- statement:
--   Let $c_*=\min\{e_0/(32000Q_S),\sigma_0/(1000Q_Q),e_0/8,1/10\}$ and $0<\nu\le c_*/10$. Let $w$ be the floored metric, $a_i$ the grid (4.2), and suppose:
--
--   1. each $N_i$ is a $\delta a_i$-cover of $T$ and satisfies (4.6);
--   2. $\Lambda\le2T_Q/\sigma_0+L/100$ (4.11);
--   3. $L/(1+\nu)\le\underline L\le L\le\overline L\le(1+\nu)L$ (4.1);
--   4. $0\le Z_i\le\Phi_i$ and $Z_i\ge\Phi_i/2-\varepsilon g_i$ (4.12);
--   5. $0\le\widehat T\le T_Q$ and $T_Q-\widehat T\le\sigma_0L/1000$ (4.15).
--
--   Then the output $\widehat C=\overline L-\max\{S/(32Q_S),\widehat T/Q_Q\}$, with $S=\sum_ia_iZ_i$, satisfies
--   $$\mathrm{OPT}\le\widehat C\le(2-c_*)\mathrm{OPT}.$$
--   This is the deterministic core of the goal theorem, with $L$ and $\mathrm{OPT}$ those of the floored metric.
--
--   Differences from the source:
--   - encoding: on the events of Lemmas 4.5 and 4.7, (4.1), (4.12), (4.15) → hypotheses on deterministic data N_i, Z_i, T̂, L̲, L̄; reason: the proposition holds pointwise on those events; no probability enters
--   - encoding: the proposition for a run of the estimator → k ≥ 3, with x₀, η_w ∈ (0,1) and β ∈ (0,1) as parameters; reason: p.19 handles k ≤ 2 directly, and flooring starts at k = 3
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Proposition 4.9, p.25, with (4.1), (4.2), p.19; (4.6), (4.9), p.23; (4.11), (4.12), p.24; (4.15), (4.16), p.25

import Mathlib
import Definitions.Def_SublinearSteiner_Estimator

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Proposition 4.9, p.25. Let `c∗ = min{e0/(32000Q_S), σ0/(1000Q_Q), e0/8, 1/10}` and `0 < ν ≤ c∗/10`. On the events of
Lemmas 4.5 and 4.7, of (4.1), and of (4.12) and (4.15), the output satisfies `OPT ≤ Ĉ ≤ (2 − c∗)OPT` for the floored metric.

**Formalization Note.**
* Every event is a hypothesis on deterministic data: `N_i`, `Z_i`, `T̂`, `L̲`, `L̄`. No probability enters.
* `k ≥ 3`, since flooring starts there (p.19 handles `k ≤ 2` directly). The floored metric, the grid and the parameters `h, ψ, H_c, A, ε, B_Q` are the
  page's, built from `w₀`, `x₀`, `η_w` and `β`. `L` and `OPT` are those of the floored metric.
* The event of Lemma 4.5 is the cover property with `ρ_i = δa_i` and (4.6). The event of Lemma 4.7 is (4.11).
* `Q_S`, `Q_Q` are as in Lemmas 4.1 and 4.2. -/
theorem proposition_4_9 {n : ℕ} (w₀ : FinMetric n) (T : Finset (Fin n)) (hk : 3 ≤ T.card) (x₀ : Fin n)
    (hx₀ : x₀ ∈ T) (ηw : ℝ) (hηw0 : 0 < ηw) (hηw1 : ηw < 1) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (Θ : ℝ) (hΘ1 : 1 ≤ Θ) (hΘω : Θ < omega) (QS QQ : ℕ)
    (hQS : 5 / 4 * omega ^ (-(QS : ℤ)) < 1 - 2 * delta) (hQQ : omega ^ (-(QQ : ℤ)) < tau / 2)
    (ν : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ cStar QS QQ / 10) (OPT L Lunder Lbar That : ℝ)
    (N : ℕ → Finset (Fin n)) (Z : ℕ → ℝ) :
    let lam := lambdaF ηw (Rmet w₀ T x₀) T.card
    let w := floored w₀ lam
    let I := gridI (Rmet w₀ T x₀) lam
    let a := gridScale lam Θ
    let h := hopBound T.card
    let ψ := psiBound T.card I β
    let A := coverA (coverHc ψ I β) ψ h I
    IsSteinerOpt T w OPT → IsTerminalMST T w L →
    (∀ i < I, IsCover w T (N i) (delta * a i) ∧
      ((N i).card : ℝ) ≤ coverHc ψ I β + 4 * ψ * h * L / (delta * a i)) →
    Lambda w T a (Finset.range I) ≤ 2 * boundedBandSum w N a I (bandCap A) / sigma0 + L / 100 →
    (L / (1 + ν) ≤ Lunder ∧ Lunder ≤ L ∧ L ≤ Lbar ∧ Lbar ≤ (1 + ν) * L) →
    (∀ i < I, 0 ≤ Z i ∧ Z i ≤ coverSaving w (N i) (a i) ∧
      (coverSaving w (N i) (a i) : ℝ) / 2 - epsA A * (N i).card ≤ Z i) →
    (0 ≤ That ∧ That ≤ boundedBandSum w N a I (bandCap A) ∧
      boundedBandSum w N a I (bandCap A) - That ≤ sigma0 * L / 1000) →
    let Chat := estimatorOutput Lbar (∑ i ∈ Finset.range I, a i * Z i) That QS QQ
    OPT ≤ Chat ∧ Chat ≤ (2 - cStar QS QQ) * OPT := by sorry

end SublinearSteiner
