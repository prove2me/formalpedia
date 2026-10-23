-- Prove2me | Theorems.Thm_RobustPMI_Hierarchy_theorem_4_9
-- name    : RobustPMI.Hierarchy.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:04.674166+00:00
-- url     : https://prove2.me/theorems/d4f5dbc3-f4e1-4c29-a773-06a5072c5556
-- title:
--   Theorem 4.9, p. 20 — under Assumptions 1–3, f_k^primal ↘ f⋆ and f_k^dual ↘ f⋆, and limits of dual minimizers give global minimizers
-- statement:
--   This is the asymptotic convergence theorem for the moment-SOS hierarchy (4.4)–(4.5) of the robust polynomial matrix inequality problem
--   $$f^\star=\inf_{y\in\mathcal Y}f(y)\quad\text{s.t.}\quad P(y,x)\succeq0\ \ \forall x\in\mathcal X .$$
--
--   Suppose (RPMIO) has an optimal solution and Assumptions 1–3 hold: $f$, $-\theta_1,\dots,-\theta_s$ are SOS-convex, $-P(\cdot,x)$ is PSD-SOS-convex for every $x\in\mathcal X$, $\mathcal X$ is compact, the quadratic module of $G$ is Archimedean in the sense of Assumption 2, and Slater's condition holds. Then:
--
--   1. $f^{\mathrm{primal}}_k\searrow f^\star$ and $f^{\mathrm{dual}}_k\searrow f^\star$ as $k\to\infty$: both sequences are non-increasing for $k\ge\lceil k_x/2\rceil$ and converge to $f^\star$.
--   2. Let $s^{(k,\star)}$ be a minimizer of (4.5) at order $k$. For any convergent subsequence $(s^{(k_i,\star)})_i$ with limit $s^\star$, the point $s^\star_e=\lim_i s^{(k_i,\star)}_e$ is a global minimizer of (RPMIO).
--   3. Consequently, if (RPMIO) has a unique global minimizer $y^\star$, then $\lim_{k\to\infty}s^{(k,\star)}_e=y^\star$.
--
--   The theorem says that the hierarchy solves the robust problem in the limit, both in value and in the minimizer, although (RPMIO) has infinitely many matrix constraints and is in general hard.
--
--   **Formalization Note** The values are extended reals and the limits are taken in the extended reals with $f^\star$ coerced. The paper presupposes that each $s^{(k,\star)}$ exists; the Lean statement takes a sequence $s^{(k)}$ that is a minimizer of (4.5) for all sufficiently large $k$. The moment vectors of (4.5) are indexed by $\mathbb N^\ell_{2\lceil k_y/2\rceil}$, so convergence of the subsequence is required on exactly those coordinates. The standing assumption of p. 2 (an optimizer exists) and the symmetry of $P$ and $G$ are hypotheses.
-- source:
--   Guo, Wang, A moment-SOS hierarchy for robust polynomial matrix inequality optimization with SOS-convexity, arXiv:2304.12628v5, p. 20, Theorem 4.9 (proof pp. 20–21)

import Mathlib
import Definitions.Def_RobustPMI_Hierarchy_Model

namespace RobustPMI.Hierarchy

open Filter Topology

/-- Theorem 4.9 (p. 20): under Assumptions 1–3 (and the standing assumption that (RPMIO) has an
optimizer),
(i) `f_k^primal ↘ f⋆` and `f_k^dual ↘ f⋆` as `k → ∞`;
(ii) if `s^{(k,⋆)}` is a minimizer of (4.5) for all large `k`, then for every convergent subsequence
`s^{(k_i,⋆)} → s⋆`, `s⋆_e` is a global minimizer of (RPMIO); consequently, if (RPMIO) has a unique
global minimizer `y⋆`, then `s_e^{(k,⋆)} → y⋆`. -/
theorem theorem_4_9 {ℓ n m q s : ℕ} (f : MvPolynomial (Fin ℓ) ℝ)
    (θ : Fin s → MvPolynomial (Fin ℓ) ℝ)
    (P : Matrix (Fin m) (Fin m) (MvPolynomial (Fin ℓ ⊕ Fin n) ℝ))
    (G : Matrix (Fin q) (Fin q) (MvPolynomial (Fin n) ℝ))
    (hP : P.IsSymm) (hG : G.IsSymm)
    (h1 : Assumption1 f θ P G) (h2 : Assumption2 G) (h3 : Assumption3 θ P G)
    (hmin : ∃ y, IsGlobalMin f θ P G y) :
    (AntitoneOn (fprimal f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      AntitoneOn (fdual f θ P G) (Set.Ici ((kx P G + 1) / 2)) ∧
      Tendsto (fprimal f θ P G) atTop (𝓝 (fstar f θ P G : EReal)) ∧
      Tendsto (fdual f θ P G) atTop (𝓝 (fstar f θ P G : EReal))) ∧
    (∀ sq : ℕ → (Fin ℓ →₀ ℕ) → ℝ, (∀ᶠ k in atTop, IsDualMinimizer f θ P G k (sq k)) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ sstar : (Fin ℓ →₀ ℕ) → ℝ,
        (∀ α ∈ monos (σ := Fin ℓ) (2 * ((ky f θ P + 1) / 2)),
          Tendsto (fun i => sq (φ i) α) atTop (𝓝 (sstar α))) →
        IsGlobalMin f θ P G (sE sstar)) ∧
    (∀ sq : ℕ → (Fin ℓ →₀ ℕ) → ℝ, (∀ᶠ k in atTop, IsDualMinimizer f θ P G k (sq k)) →
      ∀ ystar : Fin ℓ → ℝ, (∀ y, IsGlobalMin f θ P G y ↔ y = ystar) →
        Tendsto (fun k => sE (sq k)) atTop (𝓝 ystar)) := by sorry

end RobustPMI.Hierarchy
