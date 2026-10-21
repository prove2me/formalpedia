-- Prove2me | Theorems.Thm_SmoothBandit_Regret_lemma_2
-- name    : SmoothBandit.Regret.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:36.850627+00:00
-- url     : https://prove2.me/theorems/26d56e17-9620-4a4d-89f3-f5483f5aabdc
-- title:
--   Lemma 2, p. 18 — when T ≥ e^{C₀∨1}, the number of epochs is K ≤ ⌈β log T / ((2β+d) log 2)⌉
-- statement:
--   Let $K$ be the number of epochs of Algorithm 1 with horizon $T$, that is, the least integer with $\sum_{k=1}^K n_k \ge T$ for the epoch lengths $n_k$ of (10). If $T \ge e^{C_0 \vee 1}$, then
--
--   $$K \le \Big\lceil \frac{\beta}{(2\beta + d)\log 2}\log T \Big\rceil .$$
--
--   So the number of epochs grows only logarithmically in $T$; the regret analysis sums per-epoch bounds over these $K$ epochs.
--
--   **Formalization Note.** $K$ is deterministic. The statement assumes $p \le 1$, which the page's proof uses (to bound $\log(pT/4 + 1) \le \log T$) without stating it; it holds whenever the class is non-empty, by Lemma 1.
-- source:
--   Hu, Kallus & Mao, Smooth Contextual Bandits, arXiv:1909.02553v4, p. 18, Lemma 2 (proof p. 43)

import Mathlib
import Definitions.Def_SmoothBandit_Regret_Algorithm

open MeasureTheory

namespace SmoothBandit.Regret

theorem lemma_2 (d : ℕ) (hd : 1 ≤ d) (P : Params) (hP : P.Standing)
    (hp : pConst P d ≤ 1) (T : ℕ) (hT : Real.exp (max (C0 P d) 1) ≤ T) :
    numEpochs P d T ≤ ⌈P.β / ((2 * P.β + d) * Real.log 2) * Real.log T⌉₊ := by sorry

end SmoothBandit.Regret
