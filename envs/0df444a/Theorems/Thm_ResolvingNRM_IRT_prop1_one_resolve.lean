-- Prove2me | Theorems.Thm_ResolvingNRM_IRT_prop1_one_resolve
-- name    : ResolvingNRM.IRT.prop1_one_resolve
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:12.480091+00:00
-- url     : https://prove2.me/theorems/4fdf03e8-3edd-4030-8011-36dc7c4625af
-- title:
--   Proposition 1, p. 16 — one re-solve at $T - T^{5/6}$: regret of HO$^1$ is $O(Te^{-\kappa T^{1/6}})$, of IRT$^1$ is $O(Te^{-\kappa T^{1/6}}) + O(T^{5/12})$
-- statement:
--   Fix the data of the network revenue-management model: Poisson rates $\lambda_j > 0$, revenues $r_j \ge 0$ and a nonnegative bill-of-materials matrix $A$. Consider policies that re-solve the DLP once, at $t^*_1 = T - T^{5/6}$:
--
--   - $\mathrm{IRT}^1$ uses thresholded acceptance probabilities from the DLP solution $x^0 = \mathrm{sel}(C/T)$ on $[0, t^*_1)$ (probability $0$ if $x^0_j < \lambda_j T^{-1/4}$, else $1$ if $x^0_j > \lambda_j(1 - T^{-1/4})$, else $x^0_j/\lambda_j$), re-solves at $t^*_1$ with the remaining capacity $C(t^*_1)$ over the remaining time $T^{5/6}$, and uses plain probabilities $x^1_j/\lambda_j$ on $[t^*_1, T]$;
--   - $\mathrm{HO}^1$ follows $\mathrm{IRT}^1$ on $[0, t^*_1)$ and then earns the hindsight optimum of the remaining problem on $[t^*_1, T]$.
--
--   There are constants $\kappa > 0$ and $M$, depending only on $(\lambda, r, A)$, such that for every choice of optimal DLP solutions, every $T \ge 1$ and every capacity $C \ge 0$:
--   1. $v^{\mathrm{HO}}(T, C) - v^{\mathrm{HO}^1}(T, C) \le M\,T\,e^{-\kappa T^{1/6}}$;
--   2. $v^{\mathrm{HO}}(T, C) - v^{\mathrm{IRT}^1}(T, C) \le M\,T\,e^{-\kappa T^{1/6}} + M\,T^{5/12}$.
--
--   The first part is the induction step of the proof of Theorem 1 (applied on each sub-horizon $\tau_u$); the second shows that a single well-timed re-solve with thresholds already improves SPA's $O(\sqrt T)$ to $O(T^{5/12})$.
--
--   **Formalization Note** The paper gives $\kappa = \lambda_{\min}/(27(\alpha|J_\lambda|+1)^2)$ with $J_\lambda = \{j : x^*_j = \lambda_j\}$ and a constant $\alpha$ of the matrix $A$. Here $\kappa$ is an existential positive constant chosen before the selector, $T$ and $C$: $J_\lambda$ depends on $C/T$, so a constant uniform in $C$ must cover $|J_\lambda| \le n$, and the printed value of $\kappa$ is derived through Lemma 5, which is false as printed (see the mission description). The standing assumptions $\lambda > 0$, $r \ge 0$, $A \ge 0$, $C \ge 0$ are those of Sec. 2, p. 7. The horizon is a real $T \ge 1$, because the proof of Theorem 1 applies part 1 on the non-integral sub-horizons $T^{(5/6)^u}$ (eq. (10)).
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Proposition 1, p. 16 (proof in Appendix B.2, pp. 30–32)

import Mathlib
import Definitions.Def_RLPBidPrice_Unbiased_Model
import Definitions.Def_ResolvingNRM_IRT_Model

open RLPBidPrice.Unbiased Matrix

namespace ResolvingNRM.IRT

theorem prop1_one_resolve {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r lam : Fin n → ℝ)
    (hlam : ∀ j, 0 < lam j) (hr : ∀ j, 0 ≤ r j) (hA : ∀ l j, 0 ≤ A l j) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ M : ℝ, ∀ sel : (Fin m → ℝ) → (Fin n → ℝ), IsDLPSelector A r lam sel →
      ∀ T : ℝ, 1 ≤ T → ∀ C : Fin m → ℝ, 0 ≤ C →
        hindsightValue A r lam T C - hoValue A r lam sel 1 T C ≤
            M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) ∧
          hindsightValue A r lam T C - irtValue A r lam sel 1 T C ≤
            M * T * Real.exp (-κ * T ^ (1 / 6 : ℝ)) + M * T ^ (5 / 12 : ℝ) := by sorry

end ResolvingNRM.IRT
