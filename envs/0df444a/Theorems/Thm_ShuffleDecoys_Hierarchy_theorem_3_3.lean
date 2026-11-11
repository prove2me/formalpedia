-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_theorem_3_3
-- name    : ShuffleDecoys.Hierarchy.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:20.083875+00:00
-- url     : https://prove2.me/theorems/e5e007d5-f745-440a-baf8-91c3b1342635
-- title:
--   Theorem 3.3 — heterogeneous decoys leak ≥ 9p_y(1 − p_y)/(32(√(n − 1) + 2)²), and L_het(P, n), L_can(P, n) = Θ_P(1/n)
-- statement:
--   Let $P$ be a fixed non-degenerate distribution on a finite alphabet $\mathcal Y$ and $M\sim P$. For $n\ge2$ let $H_2,\dots,H_n$ be mutually independent decoys with distributions $Q_2,\dots,Q_n$, jointly independent of $M$, and $T=e_M+\sum_{i=2}^ne_{H_i}$. Then
--
--   **(5)** for every $y$ with $p_y:=P(y)\in(0,1)$,
--   $$I(M;T)\ \ge\ \frac{9p_y(1-p_y)}{32(\sqrt{n-1}+2)^2},$$
--   uniformly over all decoy distributions, including ones that depend on $n$;
--
--   **(6)** as $n\to\infty$, $L_{\mathrm{het}}(P,n)=\Theta_P(n^{-1})$ and $L_{\mathrm{can}}(P,n)=\Theta_P(n^{-1})$: there are $c,C>0$ and $N$ (depending on $P$) with $c/n\le L_{\mathrm{het}}(P,n)\le C/n$ and $c/n\le L_{\mathrm{can}}(P,n)\le C/n$ for all $n\ge N$.
--
--   Here $L_{\mathcal C}(P,n)=\inf_{A\in\mathcal C}I_P(M;Z_A)$ is the prior-specific optimal leakage of the shuffled release (Eq. (2)).
--
--   Differences from the source:
--   - encoding: "mutually independent decoys $H_i\sim Q_i$, jointly independent of $M$" → a kernel in `hetClass` (mass $\prod_iQ_i(h_i)$ at every message); reason: the same joint law.
--   - encoding: "non-degenerate" → $P(y)\ne1$ for every $y$; reason: same condition (support of size at least two).
--   - reading: $\Theta_P(n^{-1})$ → $\exists\,c,C>0,\ \exists N,\ \forall n\ge N$, both bounds for both classes with one pair $(c,C)$; reason: the standard reading, constants depending on $P$ only; one pair for both classes is equivalent (take min and max).
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), pp. 16–17, Theorem 3.3, Eqs. (5), (6)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Theorem 3.3: for a non-degenerate prior `P` on a finite alphabet `Y`, (5) every
heterogeneous mechanism with `n ≥ 2` leaks `I(M; T) ≥ 9p_y(1 − p_y)/(32(√(n − 1) + 2)²)` for
every `y` with `p_y ∈ (0, 1)`; and (6) `L_het(P, n)` and `L_can(P, n)` are both `Θ_P(1/n)`. -/
theorem theorem_3_3 {Y : Type*} [Fintype Y] [DecidableEq Y] (P : PMF Y) (hP : ∀ y, P y ≠ 1) :
    (∀ n : ℕ, 2 ≤ n → ∀ R ∈ hetClass Y n, ∀ y : Y, 0 < (P y).toReal → (P y).toReal < 1 →
      ENNReal.ofReal (9 * (P y).toReal * (1 - (P y).toReal) /
          (32 * (Real.sqrt ((n : ℝ) - 1) + 2) ^ 2)) ≤ mutualInfo (histLaw P R)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (ENNReal.ofReal (c / n) ≤ LhetP P n ∧ LhetP P n ≤ ENNReal.ofReal (C / n)) ∧
      (ENNReal.ofReal (c / n) ≤ LcanP P n ∧ LcanP P n ≤ ENNReal.ofReal (C / n))) := by sorry

end ShuffleDecoys.Hierarchy
