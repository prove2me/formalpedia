-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_lemma_5_1
-- name    : TimeDepFolk.Asymptotic.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:22.766094+00:00
-- url     : https://prove2.me/theorems/23ea20f4-bced-428b-83ca-3c5d7b458d59
-- title:
--   Lemma 5.1, p. 19 — the reward adjustments satisfy |z^j_i(a_1,…,a_L)| ≤ ε/2
-- statement:
--   Let $M>0$ bound the stage payoffs, $|g^i(a)|\le M$, and let $\varepsilon,\kappa,\eta>0$ satisfy the constraints of Part A,
--   $$\eta<\min\Big\{\frac{\varepsilon}{8M+1},\ \frac1{2M},\ \frac\kappa8,\ \frac{\kappa\varepsilon}{48M+16\varepsilon+4\kappa}\Big\}.$$
--   Let $\theta$ be an evaluation, $T$ a stage and $L=L(\eta,k,T)$ a positive integer satisfying (5.1) for $\theta[T]$. For pure action profiles $(a_1,\dots,a_L)$ define
--   $$z^j(a_1,\dots,a_L)=\diamondsuit\times p^j(a_1,\dots,a_L),\qquad \diamondsuit=\frac{\sum_{t=1}^{L}\theta_t[T]}{1-\sum_{t=1}^{L}\theta_t[T]},\quad p^j=\frac{\sum_{t=1}^{L}\theta_t[T]\,g^j(a_t)}{\sum_{t=1}^{L}\theta_t[T]} .$$
--   Then $|z^j(a_1,\dots,a_L)|\le\varepsilon/2$ for every player $j$.
--
--   The vector $z_i$ is the correction added to the reward after a punishment of player $i$, so that the punishers are indifferent to the payoffs realized during the punishment; the lemma keeps the corrected reward inside $\mathcal F$.
--
--   **Formalization Note.** The paper's $T$ is $n+1$ (0-based), so the weights are `cont θ.θ n`. On the page $M=\max|g^i(a)|$ and $\kappa=\min_i(w^i-v^i)$; here $M$ is any positive bound and $\kappa$ any positive number, which includes the page's choice. Under (5.1) the sum $\sum_{t=1}^{L}\theta_t[T]$ lies in $[0,1/2)$, so $1-\sum$ never vanishes; if the sum is $0$, Lean's $p^j$ is $0$ and the bound holds trivially, as it does for the page's $z^j=0$.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 19, Lemma 5.1 (z^j_i, ♦, p^j_i defined p. 18; constraints on η p. 17)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem lemma_5_1 {I : Type*} {A : I → Type*} (g : I → (∀ i, A i) → ℝ)
    (M : ℝ) (hM : 0 < M) (hgM : ∀ i a, |g i a| ≤ M)
    (ε κ η : ℝ) (hε : 0 < ε) (hκ : 0 < κ) (hη : 0 < η)
    (hη1 : η < ε / (8 * M + 1)) (hη2 : η < 1 / (2 * M)) (hη3 : η < κ / 8)
    (hη4 : η < κ * ε / (48 * M + 16 * ε + 4 * κ))
    (θ : Evaluation) (n L : ℕ) (hL : IsPunLength θ κ η n L)
    (a : Fin L → ∀ i, A i) (j : I) :
    |zvec g (cont θ.θ n) a j| ≤ ε / 2 := by sorry

end TimeDepFolk.Asymptotic
