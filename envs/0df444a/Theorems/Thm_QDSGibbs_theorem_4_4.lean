-- Prove2me | Theorems.Thm_QDSGibbs_theorem_4_4
-- name    : QDSGibbs.theorem_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:36:19.597829+00:00
-- url     : https://prove2.me/theorems/e83fb3c1-b346-4625-ae02-eb26eb3cced3
-- title:
--   Theorem 4.4 — Wasserstein contraction and mixing times under quantum DS
-- statement:
--   Let $(\Phi_B)_{B\in\mathcal B}$ be a finite labelled family of channels with a common fixed state $\sigma$, let $a_B>0$, and suppose the weighted quantum Dobrushin–Shlosman condition holds: $\kappa=\min_j\sum_Ba_B[1-D_{\Phi_B}(j)]>0$. Put $a=\sum_Ba_B$,
--
--   $$
--   P=\frac1a\sum_Ba_B\Phi_B,\qquad \mathcal L=\sum_Ba_B(\Phi_B-\mathrm{id})=a(P-\mathrm{id}).
--   $$
--
--   For every traceless Hermitian $X$, every $t\ge0$ and every integer $k\ge0$,
--
--   $$
--   \|P^k(X)\|_{W_1}\le(1-\kappa/a)^k\|X\|_{W_1},\qquad \|e^{t\mathcal L}(X)\|_{W_1}\le e^{-\kappa t}\|X\|_{W_1}.
--   $$
--
--   In particular $\sigma$ is the unique stationary state and, for $0<\varepsilon<1$,
--
--   $$
--   t_{\mathrm{mix}}(\mathcal L,\varepsilon)\le\kappa^{-1}\log(2N/\varepsilon),\qquad k_{\mathrm{mix}}(P,\varepsilon)\le\Big\lceil\frac a\kappa\log(2N/\varepsilon)\Big\rceil .
--   $$
--
--   This is the general contraction principle; Theorem 5.1 applies it with $a_B=1/\ell$.
--
--   **Formalization Note** $\kappa$ is any positive number with $\sum_Ba_BD_{\Phi_B}(j)+\kappa\le a$ for every $j$. Uniqueness is stated for $P$ (fixed points) and $\mathcal L$ (zeros) among states.
--
--   Differences from the source:
--   - encoding: real-valued $\|\cdot\|_{W_1}$, $D_\Psi(j)$, $\|\cdot\|_\diamond$ → values in $[0,\infty]$ (`ℝ≥0∞`); reason: the same values on the inputs the paper considers; an empty infimum or unbounded supremum gives $\infty$ instead of a junk $0$
--   - encoding: $\kappa=\min_j\sum_Ba_B[1-D_{\Phi_B}(j)]>0$ → any $\kappa>0$ with $\sum_Ba_BD_{\Phi_B}(j)+\kappa\le a$ for all $j$ (in $[0,\infty]$); reason: the paper's $\kappa$ is such a number and every conclusion weakens as $\kappa$ decreases, so the statements are equivalent
--   - encoding: "$\sigma$ is the unique stationary state" → $P\sigma=\sigma$, $\mathcal L\sigma=0$, and every state fixed by $P$ or annihilated by $\mathcal L$ equals $\sigma$; reason: stationarity of $e^{t\mathcal L}$ is $\mathcal L\rho=0$; both dynamics of the theorem are covered
--   - reading: local dimensions $2\le d_i\le d$ (standing) → local dimensions $d_i\ge2$; reason: the upper bound $d$ plays no role
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Theorem 4.4, p.30; Definition 4.3 and (4.15), p.30

import Mathlib
import Definitions.Def_QDSGibbs_w1
import Definitions.Def_QDSGibbs_tmix

open scoped Matrix ENNReal

namespace QDSGibbs

/-- **Theorem 4.4 (Wasserstein contraction and mixing times)** (arXiv:2610.03578, held file sha256
ede55815…, Theorem 4.4, p.30). Under the weighted quantum DS condition (Definition 4.3, p.30) —
a finite labelled family of channels `(Φ_B)` with common fixed state `σ`, rates `a_B > 0` and
`κ = min_j Σ_B a_B[1 − D_{Φ_B}(j)] > 0` — put `a = Σ_B a_B`, `P = a^{−1} Σ_B a_B Φ_B`,
`L = Σ_B a_B(Φ_B − id) = a(P − id)`. For every traceless Hermitian `X`, `t ≥ 0`, `k ≥ 0`:
`‖P^k(X)‖_{W1} ≤ (1 − κ/a)^k ‖X‖_{W1}` and `‖e^{tL}(X)‖_{W1} ≤ e^{−κt}‖X‖_{W1}` (4.16). In
particular `σ` is the unique stationary state and, for `0 < ε < 1`,
`t_mix(L, ε) ≤ κ^{−1} log(2N/ε)` and `k_mix(P, ε) ≤ ⌈(a/κ) log(2N/ε)⌉` (4.17).

**Formalization Note** `κ` is any real `κ > 0` with `Σ_B a_B D_{Φ_B}(j) + κ ≤ a` for every `j` (in
`ℝ≥0∞`); the paper's `κ` (the minimum over the finitely many sites) is such a number, and every
conclusion weakens as `κ` decreases, so this is equivalent. Mixing times (4.15) are `tmix`/`kmix`.
"Unique stationary state" is stated for both `P` (fixed points) and `L` (zeros) among states. -/
theorem theorem_4_4 {N : ℕ} (d : Fin N → ℕ) (hd : ∀ i, 2 ≤ d i) {ι : Type} [Fintype ι]
    (Φ : ι → Op d → Op d) (σ : Op d) (a : ι → ℝ) (κ : ℝ)
    (hΦ : ∀ B, IsChannel (Φ B) ∧ Φ B σ = σ) (hσ : IsState σ) (ha : ∀ B, 0 < a B) (hκ : 0 < κ)
    (hDS : ∀ j : Fin N,
      ∑ B, ENNReal.ofReal (a B) * influence (Φ B) j + ENNReal.ofReal κ ≤ ENNReal.ofReal (∑ B, a B)) :
    (∀ X : Op d, X.IsHermitian → X.trace = 0 →
      (∀ k : ℕ, w1 ((fun Y => ((∑ B, a B : ℝ) : ℂ)⁻¹ • ∑ B, ((a B : ℝ) : ℂ) • Φ B Y)^[k] X) ≤
          ENNReal.ofReal ((1 - κ / ∑ B, a B) ^ k) * w1 X) ∧
      (∀ t : ℝ, 0 ≤ t → w1 (sexp (fun Y => ∑ B, ((a B : ℝ) : ℂ) • (Φ B Y - Y)) t X) ≤
          ENNReal.ofReal (Real.exp (-(κ * t))) * w1 X)) ∧
    ((((∑ B, a B : ℝ) : ℂ)⁻¹ • ∑ B, ((a B : ℝ) : ℂ) • Φ B σ = σ) ∧
      (∑ B, ((a B : ℝ) : ℂ) • (Φ B σ - σ) = 0) ∧
      ∀ ρ : Op d, IsState ρ →
        ((((∑ B, a B : ℝ) : ℂ)⁻¹ • ∑ B, ((a B : ℝ) : ℂ) • Φ B ρ = ρ) → ρ = σ) ∧
        ((∑ B, ((a B : ℝ) : ℂ) • (Φ B ρ - ρ) = 0) → ρ = σ)) ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      tmix (fun Y => ∑ B, ((a B : ℝ) : ℂ) • (Φ B Y - Y)) σ ε ≤
          ENNReal.ofReal (κ⁻¹ * Real.log (2 * N / ε)) ∧
      kmix (fun Y => ((∑ B, a B : ℝ) : ℂ)⁻¹ • ∑ B, ((a B : ℝ) : ℂ) • Φ B Y) σ ε ≤
          ((⌈(∑ B, a B) / κ * Real.log (2 * N / ε)⌉₊ : ℕ) : ℕ∞) := by sorry

end QDSGibbs
