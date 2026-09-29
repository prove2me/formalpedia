-- Prove2me | Theorems.Thm_Roberts1997_RWM_chain_stays_in_Fn
-- name    : Roberts1997.RWM.chain_stays_in_Fn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:46:31.267746+00:00
-- url     : https://prove2.me/theorems/2e0316f3-297f-4067-a957-ca9e5e644ca3
-- title:
--   Lemma 2.1 — the stationary chain stays in F_n up to time t with probability → 1
-- statement:
--   Let $f$ satisfy the standing hypotheses (positive, $C^2$, a probability density, $f'/f$ Lipschitz, (A1), (A2)) and let $l>0$. For each $n$ let $X^n$ be the random walk Metropolis chain with proposal $N(x,\frac{l^2}{n-1}I_n)$ started from $\pi_n$, and $Z^n_s=X^n_{\lfloor ns\rfloor}$. Then for every fixed $t\ge0$
--
--   $$ \mathbb P\big[Z^n_s\in F_n \text{ for all } 0\le s\le t\big]\longrightarrow 1\qquad (n\to\infty), $$
--
--   where $F_n=\{|R_n-I|<n^{-1/8}\}\cap\{|S_n-I|<n^{-1/8}\}$.
--
--   This lemma says the chain spends the whole time window in the region where the uniform generator estimate of Lemma 2.6 applies, which is what lets the Ethier–Kurtz convergence theorem conclude Theorem 1.1.
--
--   **Formalization Note** The probability is the chain-law measure of the event; since $Z^n_s$ takes only the finitely many values $X^n_0,\dots,X^n_{\lfloor nt\rfloor}$ for $s\le t$, the event is a finite intersection of measurable events. The hypothesis $l>0$ is the mission-wide convention for the proposal scale.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 114, Lemma 2.1

import Definitions.Def_Roberts1997_RWM_IsRegularTarget
import Definitions.Def_Roberts1997_RWM_Chain
import Definitions.Def_Roberts1997_RWM_ProofObjects

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Roberts1997.RWM

/-- Lemma 2.1 (p. 114). For fixed `t`, the stationary chain stays in `F_n` up to time `t`:
`ℙ[Z^n_s ∈ F_n, 0 ≤ s ≤ t] → 1` as `n → ∞`. -/
theorem chain_stays_in_Fn (f : ℝ → ℝ) (hf : IsRegularTarget f) (l : ℝ) (hl : 0 < l)
    (t : ℝ≥0) :
    Tendsto (fun n : ℕ => chainLaw f n {w | ∀ s : ℝ≥0, s ≤ t → Zproc f n l s w ∈ Fn f n})
      atTop (𝓝 1) := by sorry

end Roberts1997.RWM
