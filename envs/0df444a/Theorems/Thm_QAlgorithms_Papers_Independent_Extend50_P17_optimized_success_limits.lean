-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_optimized_success_limits
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.optimized_success_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:57:48.224888+00:00
-- url     : https://prove2.me/theorems/b3f078c0-d66e-48d9-ac85-7e2286ba7d6f
-- title:
--   Eqs.(17)–(18): optimized MPBT success asymptotics
-- statement:
--   For integers $1\le k(N)\le N$ eventually, let $p_{d,\rm succ}^{\rm OMPBT}(N,k)$ be the optimum conclusive MPBT success probability at fixed local dimension $d$, optimizing both the shared resource and Alice's measurement. Bob selects and reorders distinct ports. For qubits,
--
--   $$\frac{k(N)}N\to a,\quad0<a\le1\quad\Longrightarrow\quad p_{2,\rm succ}^{\rm OMPBT}(N,k(N))\to(1-a)^3.$$
--
--   For every fixed integer $d\ge1$, if $k(N)/N\to0$, then $p_{d,\rm succ}^{\rm OMPBT}(N,k(N))\to1$. The latter is the general-dimensional consequence immediately after Eq. (17), before the qubit specialization (18). Eq. (18) and its prose give the minus sign; Table 3's $(1+a)^3$ cannot be a probability. The physical endpoint $a=1$ is included.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 6, Eqs.(17)–(18): optimized MPBT success asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Eqs.(17)–(18): both-resource-and-measurement optimized MPBT success.
The sublinear limit preceding (18) holds for every fixed dimension d ≥ 1;
the displayed linear limit is for qubits. The table's (1+a)^3 is corrected to
(1-a)^3, in agreement with Eq.(18) and its prose. -/
theorem optimized_success_limits (k : ℕ → ℕ)
    (hphysical : ∀ᶠ N in atTop, 1 ≤ k N ∧ k N ≤ N) :
    (∀ a : ℝ, 0 < a → a ≤ 1 →
      Tendsto (fun N => (k N : ℝ) / N) atTop (nhds a) →
      Tendsto (fun N => optimizedSuccess 2 N (k N)) atTop (nhds ((1-a)^3))) ∧
    (∀ d : ℕ, 1 ≤ d →
      Tendsto (fun N => (k N : ℝ) / N) atTop (nhds 0) →
      Tendsto (fun N => optimizedSuccess d N (k N)) atTop (nhds 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
