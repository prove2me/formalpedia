-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_wronskian_bc_symmetric
-- name    : TeschlQM.SturmLiouville.wronskian_bc_symmetric
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:47:41.420088+00:00
-- url     : https://prove2.me/theorems/87d940e1-8057-491a-8c80-95ae34eb98fc
-- title:
--   Lemma 9.5 — boundary Wronskian conditions
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data. Suppose $v \in \mathfrak{D}(\tau)$ with $W_a(v^*, v) = 0$, and suppose there is an $\hat f \in \mathfrak{D}(\tau)$ with $W_a(v^*, \hat f) \neq 0$. Then for all $f, g \in \mathfrak{D}(\tau)$:
--
--   1. $W_a(v, f) = 0 \iff W_a(v, f^*) = 0$;
--   2. $W_a(v, f) = W_a(v, g) = 0 \implies W_a(g^*, f) = 0$.
--
--   The second statement makes the boundary condition $W_a(v, \cdot) = 0$ symmetric (the boundary term in the Lagrange identity vanishes), which is the first step to self-adjointness in Theorem 9.6.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 186, Lemma 9.5, Eqs. (9.15)–(9.16)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
import Definitions.Def_TeschlQM_SturmLiouville_wronskian

namespace TeschlQM.SturmLiouville

/-- Teschl, Lemma 9.5, p. 186. Let `v ∈ D(τ)` with `W_a(v*, v) = 0`, and let `f̂ ∈ D(τ)` with
`W_a(v*, f̂) ≠ 0`. Then for `f, g ∈ D(τ)`:
`W_a(v, f) = 0 ⇔ W_a(v, f*) = 0` (9.15) and
`W_a(v, f) = W_a(v, g) = 0 ⇒ W_a(g*, f) = 0` (9.16). -/
theorem wronskian_bc_symmetric (L : SLData) (v fhat : ℝ → ℂ) (hv : InMaxDomain L v)
    (hvv : wronskianLeft L (fun x => starRingEnd ℂ (v x)) v = 0)
    (hfhat : InMaxDomain L fhat)
    (hne : wronskianLeft L (fun x => starRingEnd ℂ (v x)) fhat ≠ 0)
    (f g : ℝ → ℂ) (hf : InMaxDomain L f) (hg : InMaxDomain L g) :
    (wronskianLeft L v f = 0 ↔ wronskianLeft L v (fun x => starRingEnd ℂ (f x)) = 0) ∧
      (wronskianLeft L v f = 0 → wronskianLeft L v g = 0 →
        wronskianLeft L (fun x => starRingEnd ℂ (g x)) f = 0) := by sorry

end TeschlQM.SturmLiouville
