-- Prove2me | Theorems.Thm_RendezvousKn_Sym_lemma_6
-- name    : RendezvousKn.Sym.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:01.293815+00:00
-- url     : https://prove2.me/theorems/f925b5ec-3357-4397-84eb-c4154de778df
-- title:
--   Lemma 6, p. 7 — m ≥ (1 − √(α/2))n and Var X ≥ α imply P(X = 0) ≥ α²/128
-- statement:
--   Fix $n\ge2$ and tactics $\tau_A,\tau_B$, with pair set $F$, $m=|F|$, and match count $X=|F\cap E(\pi)|$ for a uniformly random binding $\pi$. Suppose that for some constant $\alpha>0$
--   $$m\ \ge\ \Bigl(1-\sqrt{\alpha/2}\Bigr)\,n\qquad\text{and}\qquad \operatorname{Var}X\ \ge\ \alpha.$$
--   Then
--   $$\mathbb P(X=0)\ \ge\ \frac{\alpha^2}{128}.$$
--
--   This is the step from variance to the no-rendezvous probability: high variance of $X$, whose mean is at most $1$, forces $X=0$ with constant probability.
--
--   **Formalization Note** The hypothesis is stated with $\ge$, as printed. The proof uses $>$; in the equality case $\alpha\le 2$ and Markov's inequality gives $\mathbb P(X=0)\ge 1-m/n=\sqrt{\alpha/2}\ge\alpha^2/128$, so the printed statement holds.
--
--   Differences from the source:
--   - encoding: Var X → E X² − (E X)² (varX); reason: the two standard expressions of the variance are equal
--   - encoding: expectation over a uniformly random binding π: [n] → [n]; rounds 1, …, n; locations [n] → average over all n! elements of Equiv.Perm (Fin n) (avgPerm); rounds and locations are Fin n, Lean round i being round i + 1; reason: the same finite uniform distribution and the same game; no instance changes
-- source:
--   Bonamy, Pilipczuk, Sereni, On the effect of symmetry requirement for rendezvous on the complete graph, arXiv:2002.03764v1, p. 7 (PDF 8), Lemma 6 (proof pp. 8–9, PDF 9–10)

import Mathlib
import Definitions.Def_RendezvousKn_Sym_Model

namespace RendezvousKn.Sym

theorem lemma_6 (n : ℕ) (hn : 2 ≤ n) (τA τB : Tactic n) (α : ℝ) (hα : 0 < α)
    (hm : (1 - Real.sqrt (α / 2)) * n ≤ ((pairSet τA τB).card : ℝ))
    (hvar : α ≤ varX (pairSet τA τB)) :
    α ^ 2 / 128 ≤ probXZero (pairSet τA τB) := by sorry

end RendezvousKn.Sym
