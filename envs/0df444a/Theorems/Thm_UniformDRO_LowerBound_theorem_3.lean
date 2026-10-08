-- Prove2me | Theorems.Thm_UniformDRO_LowerBound_theorem_3
-- name    : UniformDRO.LowerBound.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:34.388231+00:00
-- url     : https://prove2.me/theorems/36994e8d-fdb7-4c69-8ae6-e614561a7295
-- title:
--   Theorem 3, pp. 21–22 — 𝔐ₙ(𝒫, f_k) ≥ M max{(1/(8k*p_k))(√(p_k(1−p_k)/(16n)) ∧ ½(1−p_k) ∧ p_k), ⅛β_k^{1/k}c_k(ρ)(1/(4n) ∧ p_k ∧ (1−(1−β_k)^{1−k*}p_k))^{1/k*}}
-- statement:
--   Let $k \in (1,\infty)$, $k_* = k/(k-1)$, let $\rho > 0$ be arbitrary but fixed, and define
--   $$c_k(\rho) = (1 + k(k-1)\rho)^{1/k}, \qquad p_k = (1 + k(k-1)\rho)^{-1/(k-1)}, \qquad \beta_k = \frac{k(k-1)\rho}{2(1+k(k-1)\rho)} .$$
--   Fix $M > 0$, let $\mathcal P$ be the set of all distributions on $\{0, M\}$, and let $\mathfrak M_n(\mathcal P, f_k)$ be the minimax risk (16) of estimating the Cressie–Read robust risk $\mathcal R_k(Z)$, $Z \sim P_0$, from $n \ge 1$ i.i.d. observations $Z_1, \dots, Z_n \sim P_0$, over all estimators $\widehat R : \{0, M\}^n \to \mathbb R$ and all $P_0 \in \mathcal P$. Then
--   $$\mathfrak M_n(\mathcal P, f_k) \ge M \max\Biggl\{ \frac{1}{8 k_* p_k}\Bigl( \sqrt{\frac{p_k(1-p_k)}{16 n}} \wedge \tfrac12(1-p_k) \wedge p_k \Bigr),\ \ \frac18 \beta_k^{1/k} c_k(\rho) \Bigl( \frac{1}{4n} \wedge p_k \wedge \bigl(1 - (1-\beta_k)^{1-k_*} p_k\bigr) \Bigr)^{1/k_*} \Biggr\}.$$
--
--   The two branches scale as $n^{-1/2}$ and $n^{-1/k_*}$, so no estimator of the robust risk can converge faster than $n^{-1/(k_* \vee 2)}$ uniformly over distributions on two points. This matches the rate of the concentration upper bound for the plug-in robust risk (Theorem 2 of the paper), showing that the slow $n^{-1/k_*}$ rate for small $k$ is unavoidable.
--
--   **Formalization Note.** (1) The class $\mathcal P$, the estimators and the expectation $\mathbb E_{P_0^n}$ are encoded on the finite sample space $\{0,M\}^n$, and $\mathfrak M_n$ takes values in $[0,\infty]$; the robust risk is the likelihood-ratio form (3) of $\sup\{\mathbb E_Q[Z] : D_{f_k}(Q\|P_0) \le \rho\}$. (2) **Correction of the print:** the page has $8n$ inside the square root of the first branch. The paper's argument (p. 46) bounds $D_{\mathrm{kl}} \le 1/n$ and applies Pinsker in the form $\|\cdot\|_{\mathrm{TV}}^2 \le \tfrac n2 D_{\mathrm{kl}}$, which yields $\|\cdot\|_{\mathrm{TV}} \le 1/\sqrt2$, not the $\tfrac12$ that the constant $\tfrac{1}{8k_*p_k}$ requires. With $16n$ the same argument gives $D_{\mathrm{kl}} \le 1/(2n)$, $\|\cdot\|_{\mathrm{TV}} \le \tfrac12$, and exactly the printed constant. The second branch is as printed. (3) The hypothesis $n \ge 1$ is implicit on the page (the bound contains $1/n$). (4) The minimax risk agrees, for these laws, with the platform's general `HighDimStat.Minimax.minimaxRisk`.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Theorem 3, pp. 21–22 (with (16), p. 21); proof App. D.1, pp. 45–46

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

namespace UniformDRO.LowerBound

theorem theorem_3 (k ρ M : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (hM : 0 < M) (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (M * max
        (1 / (8 * UniformDRO.Concentration.kstar k * pk k ρ) *
          min (min (Real.sqrt (pk k ρ * (1 - pk k ρ) / (16 * n))) ((1 - pk k ρ) / 2)) (pk k ρ))
        (1 / 8 * βk k ρ ^ (1 / k) * UniformDRO.Concentration.ck k ρ *
          (min (min (1 / (4 * (n : ℝ))) (pk k ρ))
            (1 - (1 - βk k ρ) ^ (1 - UniformDRO.Concentration.kstar k) * pk k ρ)) ^ (1 / UniformDRO.Concentration.kstar k))) ≤
      minimaxRisk k ρ M n := by sorry

end UniformDRO.LowerBound
