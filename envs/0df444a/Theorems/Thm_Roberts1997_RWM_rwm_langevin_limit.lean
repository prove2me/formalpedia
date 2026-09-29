-- Prove2me | Theorems.Thm_Roberts1997_RWM_rwm_langevin_limit
-- name    : Roberts1997.RWM.rwm_langevin_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:50:48.436996+00:00
-- url     : https://prove2.me/theorems/2506b8e2-56fd-48fa-8192-01baaf3dbf40
-- title:
--   Theorem 1.1 — the first coordinate of the speeded-up random walk Metropolis chain converges weakly to a Langevin diffusion with speed h(l)
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be a positive $C^2$ probability density with $f'/f$ Lipschitz and satisfying (A1) $\mathbb E_f[(f'/f)^8]<\infty$ and (A2) $\mathbb E_f[(f''/f)^4]<\infty$, and let $l>0$. For $n\ge2$ let $X^n$ be the random walk Metropolis chain on $\mathbb R^n$ for the product target $\pi_n(x)=\prod_{i=1}^nf(x_i)$ with Gaussian proposal $N(x,\frac{l^2}{n-1}I_n)$, started from $\pi_n$, and let $U^n_t=X^n_{\lfloor nt\rfloor,1}$ be its first component speeded up by $n$. Then, as $n\to\infty$,
--
--   $$ U^n\Rightarrow U $$
--
--   (weak convergence in the Skorokhod topology), where $U_0$ has density $f$ and $U$ solves the Langevin SDE
--
--   $$ dU_t=h(l)^{1/2}\,dB_t+h(l)\,\frac{f'(U_t)}{2f(U_t)}\,dt,\qquad h(l)=2l^2\,\Phi\Big(-\frac{l\sqrt I}2\Big),\quad I=\mathbb E_f\Big[\Big(\frac{f'(X)}{f(X)}\Big)^2\Big]. $$
--
--   Precisely: there is a probability measure $Q$ on pairs $(u,(u^n)_{n})$ of a continuous path $u$ and càdlàg paths $u^n$ on $[0,\infty)$ such that
--
--   1. each $U^n$ ($n\ge2$) is a measurable map into path space and $u^n$ has the law of $U^n$;
--   2. $u$ is a Langevin law: $u_0$ has density $f$ and $u$ solves the martingale problem of the generator $GV=h(l)[\frac12V''+\frac12(\log f)'V']$ on $C_c^\infty$;
--   3. $Q$-almost surely, $u^n\to u$ uniformly on every compact time interval $[0,T]$.
--
--   The theorem says the Metropolis algorithm in high dimension behaves like a diffusion whose speed $h(l)$ measures its efficiency; maximising $h$ gives the optimal scaling of Corollary 1.2.
--
--   **Formalization Note** Mathlib has no Skorokhod space: weak convergence to a continuous limit is encoded as an almost-sure locally uniform coupling (the platform encoding of Ethier–Kurtz Theorem 7.4.1), which is equivalent by Skorokhod's representation theorem and Ethier–Kurtz Ch. 3, Thm 1.8, Prop. 5.3 and Prop. 7.1. "Satisfies the SDE" is read as solving the martingale problem (Ethier–Kurtz Ch. 5, Prop. 3.1, Thm 3.3). The initial condition $X^\infty_0$ of the page (components i.i.d. $f$, shared across dimensions) is read as "the $n$-th chain starts from $\pi_n$"; only the law of each $U^n$ matters. $l>0$ is the paper's implicit convention ($h(-l)\neq h(l)$). The misprint $2f(Ut)$ in (1.2) is read $2f(U_t)$. Existence of the limit is part of the claim.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 112, Theorem 1.1 (with the standing assumption 'f′/f is Lipschitz continuous', p. 111)

import Definitions.Def_Roberts1997_RWM_IsRegularTarget
import Definitions.Def_Roberts1997_RWM_Chain
import Definitions.Def_Roberts1997_RWM_Langevin

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Roberts1997.RWM

/-- Theorem 1.1 (Roberts–Gelman–Gilks 1997, p. 112). Under the standing hypotheses on `f`
and `l > 0`, the first-coordinate paths `U^n_t = X^n_{⌊nt⌋,1}` of the stationary random walk
Metropolis chains converge weakly (Skorokhod topology) to the Langevin diffusion (1.2) with
speed `h(l)` and `U_0 ~ f`. Weak convergence to a continuous limit is encoded by an almost-sure
locally uniform coupling of càdlàg copies of the `U^n` with a continuous solution `U`. -/
theorem rwm_langevin_limit (f : ℝ → ℝ) (hf : IsRegularTarget f) (l : ℝ) (hl : 0 < l) :
    ∃ Q : Measure ({x : ℝ≥0 → ℝ // Continuous x} ×
        (ℕ → {x : ℝ≥0 → ℝ // (∀ t, ContinuousWithinAt x (Set.Ici t) t) ∧
          ∀ t : ℝ≥0, 0 < t → ∃ a, Tendsto x (𝓝[<] t) (𝓝 a)})),
      IsProbabilityMeasure Q ∧
      (∀ n, 2 ≤ n → Measurable (Upath f n l)) ∧
      (∀ n, 2 ≤ n →
        Measure.map (fun z => (z.2 n).val) Q = Measure.map (Upath f n l) (chainLaw f n)) ∧
      IsLangevinLaw f l Q (fun t z => z.1.val t) ∧
      (∀ᵐ z ∂Q, ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T → |(z.2 n).val t - z.1.val t| < ε) := by sorry

end Roberts1997.RWM
