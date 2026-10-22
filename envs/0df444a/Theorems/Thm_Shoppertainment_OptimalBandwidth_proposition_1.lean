-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_proposition_1
-- name    : Shoppertainment.OptimalBandwidth.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:49:57.664511+00:00
-- url     : https://prove2.me/theorems/ea070166-9a6a-466f-9859-4ce01bd722eb
-- title:
--   Proposition 1, p. 25 — the low-pricing proportion ψ(te) = (q̂ − q̲)/(1 − q̲) for te > t̂e, else 0; increasing in te, decreasing in q̲
-- statement:
--   Let the manufacturers' qualities be uniform on $[\underline q, 1]$ with $0 \le \underline q < 1$, and let $\psi(t_e)$ be the proportion of them that price low under Lemma 2's rule, i.e. those with $1/(2-q) < t_e$. Write $\hat t_e = 1/(2-\underline q)$ and $\hat q = 2 - 1/t_e$.
--
--   1. For every $t_e \in [0,1]$,
--   $$\psi(t_e) = \begin{cases} \dfrac{\hat q - \underline q}{1 - \underline q} = \dfrac{2 - 1/t_e - \underline q}{1 - \underline q} & \text{if } t_e > \hat t_e,\\[2mm] 0 & \text{if } t_e \le \hat t_e.\end{cases}$$
--   2. $\psi$ is strictly increasing in $t_e$ on $(\hat t_e, 1]$.
--   3. For each fixed $t_e \in [0,1]$, $\psi$ is non-increasing in $\underline q$ over the thresholds $\underline q \in [0,1)$ with $t_e > \hat t_e(\underline q)$, and strictly decreasing there when $t_e < 1$.
--
--   The result quantifies how the streamer's bandwidth allocation steers the manufacturers' pricing.
--
--   **Formalization Note** The proportion is the Lebesgue measure of $\{q \in [\underline q, 1] : 1/(2-q) < t_e\}$ divided by $1 - \underline q$. The decrease in $\underline q$ is strict for $t_e < 1$ and only weak at $t_e = 1$: there every manufacturer of quality below $1$ prices low and $\psi \equiv 1$, so the decrease cannot be strict. The threshold $\underline q < 1$ is pinned so that the uniform law on $[\underline q,1]$ exists.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 25, Proposition 1, display (11); proof in Online Supplementary A.2, p. S3 (PDF 52)

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem proposition_1 (ql : ℝ) (hql : 0 ≤ ql) (hql1 : ql < 1) :
    (∀ te ∈ Set.Icc (0:ℝ) 1,
        psi ql te = if teHat ql < te then (qHat te - ql) / (1 - ql) else 0) ∧
    StrictMonoOn (psi ql) (Set.Ioc (teHat ql) 1) ∧
    (∀ te ∈ Set.Icc (0:ℝ) 1,
        AntitoneOn (fun ql' => psi ql' te) {ql' : ℝ | 0 ≤ ql' ∧ ql' < 1 ∧ teHat ql' < te} ∧
        (te < 1 →
          StrictAntiOn (fun ql' => psi ql' te) {ql' : ℝ | 0 ≤ ql' ∧ ql' < 1 ∧ teHat ql' < te})) := by sorry

end Shoppertainment.OptimalBandwidth
