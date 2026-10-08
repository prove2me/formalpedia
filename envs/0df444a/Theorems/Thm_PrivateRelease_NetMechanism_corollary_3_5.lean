-- Prove2me | Theorems.Thm_PrivateRelease_NetMechanism_corollary_3_5
-- name    : PrivateRelease.NetMechanism.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:09:19.692595+00:00
-- url     : https://prove2.me/theorems/2a71760b-ef93-4a2d-85e1-d7da2faf58fb
-- title:
--   Corollary 3.5 — for counting queries the Net mechanism is (2α, δ)-useful once α ≥ (2/(εn)) log(|N_α(C)|/δ)
-- statement:
--   Let $X$ be a finite data universe, $n\ge1$ the input size, and $C$ a class of predicates $\varphi:X\to\{0,1\}$ with counting queries $Q_\varphi$. Let $N$ be a minimum $\alpha$-net for $\{Q_\varphi:\varphi\in C\}$. If $\varepsilon>0$, $0<\delta\le1$ and
--   $$
--   \alpha\ \ge\ \frac{2}{\varepsilon n}\,\log\frac{|N|}{\delta},
--   $$
--   then the Net mechanism run on $N$ is $(2\alpha,\delta)$-useful for $C$: for every input $z\in X^n$, with probability at least $1-\delta$ its output $\hat D$ satisfies $|Q_\varphi(\hat D)-Q_\varphi(z)|\le2\alpha$ for every $\varphi\in C$.
--
--   It reduces the utility of the Net mechanism for counting queries to a bound on the size of minimum α-nets, which Theorems 3.6 and 3.9 supply.
--
--   **Formalization Note** The paper's "$\log N_\alpha(C)/\delta$" is the logarithm of $|N_\alpha(C)|/\delta$. No positivity hypothesis on the quality score's sensitivity $GS_q$ is needed here: when $GS_q=0$ the mechanism is uniform on $N$ (Lean's $x/0=0$), and for counting queries this happens only when $2\alpha\ge1$ or every query of $C$ is constant, where every output is accurate. Neighbours differ in exactly one entry.
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 9, Corollary 3.5

import Mathlib
import Definitions.Def_PrivateRelease_NetMechanism_ExpMech

namespace PrivateRelease.NetMechanism

/-- Corollary 3.5 (p. 9): for any class `C` of counting queries on inputs of size `n ≥ 1`, the
Net mechanism run on a minimum α-net `N` is `(2α, δ)`-useful whenever
`α ≥ (2/(εn)) log(|N|/δ)`. -/
theorem corollary_3_5 {X : Type} [Fintype X] {n : ℕ} (hn : 1 ≤ n) (C : Set (X → Bool))
    (ε α δ : ℝ) (N : Finset (Database X)) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hN : IsMinNet (countingClass C) α N)
    (hα : 2 / (ε * n) * Real.log ((N.card : ℝ) / δ) ≤ α) :
    Useful (countingClass C) (2 * α) δ (netMech (n := n) (countingClass C) ε N) := by sorry

end PrivateRelease.NetMechanism
