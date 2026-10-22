-- Prove2me | Theorems.Thm_QZeroSum19_LPReduce_lemma_12_small
-- name    : QZeroSum19.LPReduce.lemma_12_small
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:13.146924+00:00
-- url     : https://prove2.me/theorems/175944b9-e285-4313-bffc-71860b4f8dee
-- title:
--   Proof of Lemma 12, p. 14 — case λ* ≤ 2ε‴: OPT ≥ α − 6R(r+1)ε‴ = α − ε (added |α| ≤ R; (6) row 2 corrected)
-- statement:
--   Let the LP pair (4)/(5) with data $A \in \mathbb R^{n\times m}$, $b$, $c$ satisfy the standing assumptions of §4 with constants $R$, $r$ and optimal value $\mathrm{OPT}$, let $\alpha \in \mathbb R$ with $|\alpha| \le R$, let $\varepsilon > 0$ and $\varepsilon''' = \varepsilon/(6R(r+1))$, and let $\lambda^*$ be the value of the game (6) (second row $(-e^{\mathsf T}, -1, 1)$). Then
--   $$\lambda^* \le 2\varepsilon''' \implies \mathrm{OPT} \ge \alpha - 6R(r+1)\varepsilon''' = \alpha - \varepsilon .$$
--
--   This is the second case of the proof of Lemma 12: a small game value certifies that the LP reaches the objective level $\alpha$ up to the additive error $\varepsilon$.
--
--   **Formalization Note** The hypothesis $|\alpha| \le R$ is not written in the lemma; the proof's step (7) needs it (see the item for (7)–(8)), and the context of §4 supplies it ($-R \le \mathrm{OPT} \le R$ for the binary search; entries of (6) in $[-1,1]$).
-- source:
--   van Apeldoorn and Gilyén, Quantum algorithms for zero-sum games, arXiv:1904.03180v1, p. 14, proof of Lemma 12, second case ("OPT ≥ α − 6R(r + 1)ε‴ = α − ε")

import Mathlib
import Definitions.Def_QZeroSum19_LPReduce_Setting

open Matrix

namespace QZeroSum19.LPReduce
theorem lemma_12_small {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (R r OPT α ε : ℝ) (hLP : LPStanding A b c R r OPT) (hα : |α| ≤ R) (hε : 0 < ε) :
    QZeroSum19.GK.gameValue (gameMatrix A b c α R) ≤ 2 * epsGame ε R r → α - ε ≤ OPT := by sorry
end QZeroSum19.LPReduce
