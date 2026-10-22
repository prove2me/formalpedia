-- Prove2me | Theorems.Thm_Shoppertainment_OptimalBandwidth_lemma_2
-- name    : Shoppertainment.OptimalBandwidth.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:49:58.1256+00:00
-- url     : https://prove2.me/theorems/011d842c-373c-4dbe-9216-f08c5cf963f1
-- title:
--   Lemma 2, p. 24 — a manufacturer of quality q prices low (pL) iff te > 1/(2 − q), else high (pH)
-- statement:
--   Consider a manufacturer of quality $q \in (0, 1]$ selling through the streamer, with commission rate $\alpha \in (0,1)$, good-fit value $v > 0$, attending traffic $T > 0$ and entertainment bandwidth $t_e \in [0,1]$. Its profit at price $p > 0$ is $\pi_M(p) = (1-\alpha)\,p\,D(p)$, with the demand $D$ of (8) built from $p_H = (1 - t_e + t_e q)v$ and $p_L = t_e q v$.
--
--   1. If $t_e > 1/(2 - q)$, then $p_L > 0$ and $p_L$ is the **unique** profit-maximizing price:
--   $$\pi_M(p) < \pi_M(p_L) \quad \text{for every } p > 0,\ p \ne p_L.$$
--   2. If $t_e \le 1/(2-q)$, then $p_H > 0$ and $p_H$ maximizes profit: $\pi_M(p) \le \pi_M(p_H)$ for every $p > 0$.
--
--   This is the manufacturers' equilibrium pricing rule. It is the only place where their decision enters the model, and it is what the consumer surplus and the streamer's profitability are built from.
--
--   **Formalization Note** The printed display (10) reads $\hat t_e = 1/(2-\underline q)$, with the quality threshold $\underline q$, for a manufacturer of quality $q$. The proof in Online Supplementary A.2 (p. S3) and Figure 4(b) use the manufacturer's own threshold $1/(2-q)$, and the printed reading would make every manufacturer price low once $t_e > 1/(2-\underline q)$, contradicting Proposition 1. The statement therefore uses $1/(2-q)$. Two hypotheses are pinned: $0 < q$ (at $q = 0$ every positive price earns $0$ and $p_L = 0$ is not an admissible price, since prices are positive, p. 13), and $0 < T$ (at $T = 0$ every price earns $0$ and $p_L$ is not the unique maximizer). At $t_e = 1/(2-q)$ both prices earn the same profit, so only maximality of $p_H$ is claimed in the second case.
-- source:
--   Gu, Zhao & Wu, A Model of Shoppertainment Live Streaming, accepted manuscript (Management Science, forthcoming, Oct. 2024), p. 24, Lemma 2, display (10); proof in Online Supplementary A.2, p. S3 (PDF 52)

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

namespace Shoppertainment.OptimalBandwidth

theorem lemma_2 (α v te q T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hT : 0 < T)
    (hq : 0 < q) (hq1 : q ≤ 1) (hte : te ∈ Set.Icc (0:ℝ) 1) :
    (1 / (2 - q) < te → 0 < pL v te q ∧ ∀ p : ℝ, 0 < p → p ≠ pL v te q →
        mfrProfit α v te q T p < mfrProfit α v te q T (pL v te q)) ∧
    (te ≤ 1 / (2 - q) → 0 < pH v te q ∧ ∀ p : ℝ, 0 < p →
        mfrProfit α v te q T p ≤ mfrProfit α v te q T (pH v te q)) := by sorry

end Shoppertainment.OptimalBandwidth
