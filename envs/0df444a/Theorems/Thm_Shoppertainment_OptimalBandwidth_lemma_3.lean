-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_lemma_3
-- name    : Shoppertainment.OptimalBandwidth.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:09.326361+00:00
-- url     : https://prove2.me/theorems/0a031b67-6d7a-4e47-964b-eaa32d8f4488
-- title:
--   Lemma 3, p. 27 — the consumer's expected shopping surplus is Eu_p = ∫_{q̲}^{q̂} (1 − te) q v dF(q) for te > t̂e, else 0
-- statement:
--   Let $v > 0$ and $0 \le \underline q < 1$, with qualities uniform on $[\underline q, 1]$ ($dF(q) = dq/(1-\underline q)$). Let $Eu_p(t_e)$ be an attending consumer's expected surplus from shopping when every manufacturer prices according to Lemma 2. Then for every $t_e \in [0,1]$,
--   $$Eu_p(t_e) = \begin{cases} \displaystyle\frac{1}{1-\underline q}\int_{\underline q}^{\hat q} (1 - t_e)\,q\,v\,dq & \text{if } t_e > \hat t_e,\\[2mm] 0 & \text{if } t_e \le \hat t_e,\end{cases}$$
--   where $\hat t_e = 1/(2-\underline q)$ and $\hat q = 2 - 1/t_e$.
--
--   Consumers gain from shopping only through "deal prices" $p_L$, which exist only when the entertainment bandwidth exceeds $\hat t_e$. This closed form feeds the attending traffic (13).
--
--   **Formalization Note** $Eu_p$ is defined from the consumer's ex-ante surplus $q\max(p_H - p, 0) + (1-q)\max(p_L - p, 0)$ at the equilibrium price $p$ of each manufacturer, averaged over the uniform law; the statement is therefore a genuine computation, not a definition. $\underline q < 1$ is pinned for the uniform law.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 27, Lemma 3, display (12); surplus derivation p. 26

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem lemma_3 (v ql : ℝ) (hv : 0 < v) (hql : 0 ≤ ql) (hql1 : ql < 1) :
    ∀ te ∈ Set.Icc (0:ℝ) 1, Eup v ql te =
      if teHat ql < te then (1 / (1 - ql)) * ∫ q in ql..qHat te, (1 - te) * q * v else 0 := by sorry

end Shoppertainment.OptimalBandwidth
