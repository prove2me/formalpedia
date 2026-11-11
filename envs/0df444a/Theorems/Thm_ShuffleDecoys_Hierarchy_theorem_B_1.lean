-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_theorem_B_1
-- name    : ShuffleDecoys.Hierarchy.theorem_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:48.119618+00:00
-- url     : https://prove2.me/theorems/50f370c8-fe52-4b0b-bea1-8bca8e1298fd
-- title:
--   Theorem B.1 — prior-independent optimal leakage: L_can, L_het = Θ_d(1/n), L_obl = Θ_d(1/n²), L_dep(d, n) = [log(d/n)]₊
-- statement:
--   A genuine message $M\sim P$ on $[d]$ is released together with $n-1$ decoys over $[d]$ under a uniformly random permutation of the $n$ positions. For a class $\mathcal C$ of decoy mechanisms (canonical, heterogeneous, message-oblivious, message-dependent) let
--   $$L_{\mathcal C}(d,n)=\inf_{A\in\mathcal C}\ \sup_{P\in\Delta_d}I_P(M;Z_A)$$
--   be the minimax leakage in nats, the supremum over all priors on $[d]$. Then for every fixed $d\ge2$ there are constants $0<c\le C$ and $N$, depending on $d$ only, such that for all $n\ge N$
--   $$\frac cn\le L_{\mathrm{can}}(d,n)\le\frac Cn,\qquad \frac cn\le L_{\mathrm{het}}(d,n)\le\frac Cn,\qquad \frac c{n^2}\le L_{\mathrm{obl}}(d,n)\le\frac C{n^2},$$
--   that is $L_{\mathrm{can}}(d,n)=\Theta_d(n^{-1})$, $L_{\mathrm{het}}(d,n)=\Theta_d(n^{-1})$, $L_{\mathrm{obl}}(d,n)=\Theta_d(n^{-2})$ as $n\to\infty$; and for all integers $d\ge2$, $n\ge2$,
--   $$L_{\mathrm{dep}}(d,n)=\big[\log(d/n)\big]_+,\qquad [x]_+:=\max\{x,0\}.$$
--   Independent decoys cannot beat order $1/n$, correlated message-oblivious decoys reach order $1/n^2$ and no better, and decoys that may depend on the message give perfect secrecy exactly when $n\ge d$.
--
--   Differences from the source:
--   - reading: $\Theta_d(\cdot)$ as $n\to\infty$ → $\exists\,0<c\le C,\ \exists N,\ \forall n\ge N$, lower and upper bounds for all three classes with one pair $(c,C)$; reason: the standard reading with constants depending on $d$ only; one pair for the three clauses is equivalent (take min and max).
--   - encoding: infimum and supremum in $\mathbb R$ → in $[0,\infty]$ (`ℝ≥0∞`), real bounds embedded by `ENNReal.ofReal`; reason: every leakage is finite (at most $\log d$), so the values are the same, and the extended infimum and supremum are always the true ones.
--   - encoding: mechanisms, priors, release → decoy kernels on `Fin (n - 1) → Fin d`, priors `PMF (Fin d)` (closed simplex), release law `shuffleLaw`; reason: Lean conventions for the paper's objects.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 45, Theorem B.1, Eq. (33); announced p. 7, Eq. (3)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Theorem B.1: for every `d ≥ 2` there are `0 < c ≤ C` and `N` with, for all `n ≥ N`,
`c/n ≤ L_can(d, n) ≤ C/n`, `c/n ≤ L_het(d, n) ≤ C/n`, `c/n² ≤ L_obl(d, n) ≤ C/n²`; and for all
`d, n ≥ 2`, `L_dep(d, n) = max{log(d/n), 0}` (nats). -/
theorem theorem_B_1 :
    (∀ d : ℕ, 2 ≤ d → ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (ENNReal.ofReal (c / n) ≤ Lcan d n ∧ Lcan d n ≤ ENNReal.ofReal (C / n)) ∧
      (ENNReal.ofReal (c / n) ≤ Lhet d n ∧ Lhet d n ≤ ENNReal.ofReal (C / n)) ∧
      (ENNReal.ofReal (c / (n : ℝ) ^ 2) ≤ Lobl d n ∧
        Lobl d n ≤ ENNReal.ofReal (C / (n : ℝ) ^ 2))) ∧
    (∀ d n : ℕ, 2 ≤ d → 2 ≤ n →
      Ldep d n = ENNReal.ofReal (max (Real.log ((d : ℝ) / n)) 0)) := by sorry

end ShuffleDecoys.Hierarchy
