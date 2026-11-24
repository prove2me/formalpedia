-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_Supplement_theorem_5_2
-- name    : RobustPMI.Hierarchy.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:47:33.110135+00:00
-- url     : https://prove2.me/theorems/abd74e8b-f664-475b-bf68-f747d1ec571b
-- title:
--   Theorem 5.2, p. 29 — convex setting: the hierarchy (5.1)–(5.2) converges to f⋆ and limits of s_e^{(k,⋆)} are minimizers
-- statement:
--   Consider the hierarchy (5.1)–(5.2) for (RPMIO), in which the quadratic module $\mathcal Q_k(\Theta)$ and the moment cone $\mathcal M_k(\Theta)$ have the relaxation order $k$. Suppose Assumptions 2 (Archimedean), 3 (Slater), 4(i) (ball constraint $\theta_1=b^2-\|y\|^2$) and 5 ($f$, $-\theta_j$ convex, $-P(\cdot,x)$ PSD-convex for $x\in\mathcal X$, $\mathcal X$ compact) hold, and that (RPMIO) has an optimal solution. Then
--
--   1. $\lim_{k\to\infty}f_k^{\mathrm{primal}}=\lim_{k\to\infty}f_k^{\mathrm{dual}}=f^\star$;
--   2. if $s^{(k,\star)}$ is a minimizer of (5.2) for every sufficiently large $k$, then $(s_e^{(k,\star)})_k$ has a convergent subsequence, and for every convergent subsequence $(s_e^{(k_i,\star)})_i$ the limit is a global minimizer of (RPMIO). Consequently, if (RPMIO) has a unique global minimizer $y^\star$, then $s_e^{(k,\star)}\to y^\star$.
--
--   Unlike Theorem 4.9, the convergence need not be monotone (Remark 5.3).
--
--   Differences from the source:
--   - reading: the theorem's own hypotheses (the paper assumes once, on p. 2, that the optimal set of (RPMIO) is nonempty) → hypothesis ∃ y, IsGlobalMin f θ P G y; reason: the p. 2 standing assumption governs every statement about f⋆; without it the real infimum f⋆ is a junk value
--   - reading: each s^{(k,⋆)} a minimizer of (5.2) → s^{(k,⋆)} a minimizer for all sufficiently large k (∀ᶠ k in atTop); reason: the minimizers need only exist from some order on, as the paper presupposes; same reading as the published Theorem 4.9
--   - encoding: limits of values in ℝ ∪ {±∞} → Tendsto in EReal; reason: Lean convention
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 29, Theorem 5.2

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model
import Definitions.Def_RobustPMI_Hierarchy_Supplement_Model

namespace RobustPMI.Hierarchy.Supplement

open MvPolynomial Matrix Filter Topology

/-- Theorem 5.2 (p. 29): under Assumptions 2, 3, 4(i) and 5 (and the standing assumption that
(RPMIO) has an optimizer), for the hierarchy (5.1)–(5.2):
(i) `lim_k f_k^primal = lim_k f_k^dual = f⋆`;
(ii) if `s^{(k,⋆)}` is a minimizer of (5.2) for all large `k`, then `(s_e^{(k,⋆)})_k` has a
convergent subsequence, the limit of every convergent subsequence `(s_e^{(k_i,⋆)})_i` is a global
minimizer of (RPMIO), and if (RPMIO) has a unique global minimizer `y⋆` then `s_e^{(k,⋆)} → y⋆`. -/
theorem theorem_5_2 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h2 : Assumption2 G) (h3 : Assumption3 θ P G) (h4 : Assumption4i θ)
    (h5 : Assumption5 f θ P G) (hmin : ∃ y, IsGlobalMin f θ P G y) :
    (Tendsto (fprimal5 f θ P G) atTop (𝓝 (fstar f θ P G : EReal)) ∧
      Tendsto (fdual5 f θ P G) atTop (𝓝 (fstar f θ P G : EReal))) ∧
    (∀ sq : ℕ → (Fin ℓ →₀ ℕ) → ℝ, (∀ᶠ k in atTop, IsDualMinimizer5 f θ P G k (sq k)) →
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ y : Fin ℓ → ℝ,
        Tendsto (fun i => sE (sq (φ i))) atTop (𝓝 y)) ∧
      (∀ φ : ℕ → ℕ, StrictMono φ → ∀ y : Fin ℓ → ℝ,
        Tendsto (fun i => sE (sq (φ i))) atTop (𝓝 y) → IsGlobalMin f θ P G y) ∧
      (∀ ystar : Fin ℓ → ℝ, (∀ y, IsGlobalMin f θ P G y ↔ y = ystar) →
        Tendsto (fun k => sE (sq k)) atTop (𝓝 ystar))) := by sorry

end RobustPMI.Hierarchy.Supplement
