-- Prove2me | Theorems.Thm_SLQSolv_MinSeq_zero_extension
-- name    : SLQSolv.MinSeq.zero_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:21:14.309706+00:00
-- url     : https://prove2.me/theorems/d604000a-201b-4144-9305-089bdb12a106
-- title:
--   §4, proof of Proposition 4.1, (4.3), p. 2284 — the zero extension lies in 𝒰[0, T] and J⁰(t, 0; u) = J⁰(0, 0; 0I_[0,t) ⊕ u)
-- statement:
--   Assume (H1)–(H2), let $t\in[0,T)$ and $u\in\mathcal U[t,T]$. The **zero extension** of $u$ is $[0I_{[0,t)}\oplus u](s)=0$ for $s<t$ and $=u(s)$ for $s\ge t$. It is an admissible control on $[0,T]$, and
--
--   $$
--   J^0(t,0;u)=J^0\big(0,0;0I_{[0,t)}\oplus u\big).
--   $$
--
--   Starting from the zero state with no control, the state stays $0$ on $[0,t]$, so the problem on $[t,T]$ embeds in the problem on $[0,T]$. This carries positivity, and hence convexity, of $J^0$ from the initial time $0$ to any $t$.
--
--   **Formalization Note** The page displays the identity followed by an inequality under uniform convexity; only the identity, together with the admissibility the page asserts just before it, is stated. (H1)–(H2) are the standing assumptions; the state, cost, value function and optimality notions are those of the shared `Setting` module.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), §4, proof of Proposition 4.1, (4.3) and the display following it, p. 2284

import Mathlib
import Definitions.Def_SLQSolv_MinSeq_Sequence

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix

namespace SLQSolv.MinSeq

/-- §4, proof of Proposition 4.1, (4.3), p. 2284: for `t ∈ [0, T)` and `u ∈ 𝒰[t, T]`, the zero
extension `0I_{[0,t)} ⊕ u` lies in `𝒰[0, T]` and `J⁰(t, 0; u) = J⁰(0, 0; 0I_{[0,t)} ⊕ u)`. -/
theorem zero_extension {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (t : ℝ≥0) (ht : t < d.T) (u : ℝ≥0 → Ω → Fin m → ℝ) (hu : Adm Bs d t u) :
    Adm Bs d 0 (fun s ω => if t ≤ s then u s ω else 0) ∧
      J0 Bs d t 0 u = J0 Bs d 0 0 (fun s ω => if t ≤ s then u s ω else 0) := by sorry

end SLQSolv.MinSeq
