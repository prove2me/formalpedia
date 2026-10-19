-- Prove2me | Theorems.Thm_RedundancyStab_IID_eq_14_ps_drift
-- name    : RedundancyStab.IID.eq_14_ps_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:04.69721+00:00
-- url     : https://prove2.me/theorems/da347499-53d1-44f2-8f8d-69f2724cb508
-- title:
--   (14), PS, p. 26 — the drift of M_s in state n⃗ is λd/K − µ Σ_{c∈C(s)} Σ_{l∈c} n_c/m_l
-- statement:
--   Consider the PS chain of the redundancy-$d$ model with i.i.d. $\mathrm{Exp}(\mu)$ copies, $1\le d\le K$, $\lambda>0$, $\mu>0$, with exit rate $q(\vec n)$ and jump matrix $G(\vec n,\cdot)$. For every state $\vec n\in\mathbb N^C$ and every server $s$, the drift of the number of copies $M_s$ at server $s$ is
--   $$\tilde f_s(\vec n)=\sum_{\vec y} q(\vec n)\,G(\vec n,\vec y)\,\big(M_s(\vec y)-M_s(\vec n)\big)=\frac{\lambda d}{K}-\mu\sum_{c\in C(s)}\sum_{l\in c}\frac{n_c}{m_l},$$
--   where $m_l=M_l(\vec n)=\sum_{c\in C(l)}n_c$.
--
--   This is the one-step drift that the proof of Lemma 2 evaluates at a most-loaded server.
--
--   **Formalization Note** The drift is written with the generator of the published CTMC representation, $q(\vec n)G(\vec n,\vec y)$, as a `tsum` over states (only finitely many terms are nonzero). Lean's $n_c/0=0$ agrees with the paper since $m_l\ge n_c$ for $l\in c$. Under ROS the departure rate in (1) is only an average, so (14) is stated for PS only.
-- source:
--   Anton, Ayesta, Jonckheere & Verloop, On the stability of redundancy models, arXiv:1903.04414v2, p. 26, proof of Lemma 2, display (14), using display (1) of p. 6

import Mathlib
import Definitions.Def_RedundancyStab_IID_Model

namespace RedundancyStab.IID

theorem eq_14_ps_drift (K d : ℕ) (hd : 1 ≤ d) (hdK : d ≤ K) (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (n : PSState K d) (s : Fin K) :
    ∑' y : PSState K d, psRate K d lam μ n * (psJump K d lam μ n y).toReal *
        ((copies K d y s : ℝ) - (copies K d n s : ℝ)) =
      lam * d / K - μ * ∑ c ∈ typesAt K d s, ∑ l ∈ c.1, (n c : ℝ) / (copies K d n l : ℝ) := by sorry

end RedundancyStab.IID
