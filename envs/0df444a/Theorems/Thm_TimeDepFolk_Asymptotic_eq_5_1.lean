-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_eq_5_1
-- name    : TimeDepFolk.Asymptotic.eq_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:14.193062+00:00
-- url     : https://prove2.me/theorems/26090b53-c6d9-41c7-aec9-b73d69038b13
-- title:
--   (5.1), p. 17 — a punishment length L(η,k,T) ≥ 1 with 3η/κ ≤ Σ_{t=1}^{L+1} θ^k_t[T] < 4η/κ exists
-- statement:
--   Let $\theta$ be an evaluation, $T\ge1$ a stage, and $\kappa,\eta>0$ with $\eta<\kappa/8$ and $\eta<1/\kappa$. Suppose $\theta_1[T]\le\eta^2$. Then there is a positive integer $L=L(\eta,k,T)$ with
--   $$\frac{3\eta}{\kappa}\le\sum_{t=1}^{L+1}\theta_t[T]<\frac{4\eta}{\kappa}. \tag{5.1}$$
--
--   $L$ is the length of the punishment phase started at stage $T$: long enough to deter a deviation, short enough for the subsequent reward to motivate the punishers.
--
--   **Formalization Note.** The paper's $T$ is $n+1$ (0-based): the weights are `cont θ.θ n`, and $\sum_{t=1}^{L+1}$ is `∑ t ∈ range (L + 1)`. The constraints $\eta<\kappa/8$ and $\eta<1/\kappa$ are those of Part A ($\eta<1/(2M)\le1/\kappa$). The hypothesis that the tail $\sum_{s\ge T}\theta_s$ is positive is an addition: the page treats $\theta[T]$ as an evaluation, which presupposes it, and for a patient sequence it holds once $k$ is large. Without it `cont` is identically $0$ and no such $L$ exists.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 17, §5.1 Part A, (5.1)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem eq_5_1 (θ : Evaluation) (n : ℕ) (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η)
    (hηκ : η < κ / 8) (hηκ' : η < 1 / κ) (htail : 0 < ∑' r, θ.θ (n + r))
    (hθ1 : cont θ.θ n 0 ≤ η ^ 2) :
    ∃ L : ℕ, IsPunLength θ κ η n L := by sorry

end TimeDepFolk.Asymptotic
