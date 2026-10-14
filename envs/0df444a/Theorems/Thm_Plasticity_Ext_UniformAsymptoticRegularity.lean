-- Prove2me | Theorems.Thm_Plasticity_Ext_UniformAsymptoticRegularity
-- name    : Plasticity.Ext.UniformAsymptoticRegularity
-- status  : Proved
-- author  : @scanstone
-- created : 2026-10-14T07:54:18.097608+00:00
-- url     : https://prove2.me/theorems/c5dcf8b5-fa28-4f1f-a7d8-d036fdc2240b
-- title:
--   Uniform asymptotic regularity of averaged nonexpansive maps (Edelstein–O’Brien)
-- statement:
--   Let $C$ be a bounded convex subset of a real normed space, let $K\colon C\to C$ be nonexpansive, let $0<\alpha<1$, and let $P=(1-\alpha)I+\alpha K$ be the averaged map. Then
--   $$\sup_{x\in C}\bigl\|P^{n+1}(x)-P^{n}(x)\bigr\|\longrightarrow0\qquad(n\to\infty);$$
--   that is, for every $\varepsilon>0$ there is $N$ such that $\|P^{n+1}(x)-P^n(x)\|\le\varepsilon$ for all $n\ge N$ and all $x\in C$.
--
--   Ishikawa (1976) proved the convergence for each $x$; Edelstein and O’Brien proved that it is uniform on $C$, and Goebel and Kirk made it uniform also over all nonexpansive $K$. A consequence used in A01: if $P$ maps $C$ onto $C$, then $P$ is the identity.
--
--   **Formalization Note** $K$ is a function on the whole space, constrained on $C$ by `Set.MapsTo` and `LipschitzOnWith 1`; $P^n$ is the $n$-fold iterate `P^[n]`.
-- source:
--   M. Edelstein and R. C. O'Brien, Nonexpansive mappings, asymptotic regularity and successive approximations, J. London Math. Soc. (2) 17 (1978), 547–554 (uniformity on C for constant step); K. Goebel and W. A. Kirk, Iteration processes for nonexpansive mappings, Contemp. Math. 21 (1983), 115–123; S. Ishikawa, Proc. Amer. Math. Soc. 59 (1976), 65–71; as used in Borzdyński–Wiśnicki, J. Fixed Point Theory Appl. 18 (2016), arXiv:1511.04069, Lemma 3.1

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

namespace Plasticity.Ext
theorem UniformAsymptoticRegularity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hconv : Convex ℝ C) (hbdd : Bornology.IsBounded C)
    (K : E → E) (hmaps : Set.MapsTo K C C) (hlip : LipschitzOnWith 1 K C)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ C,
      ‖(fun z => (1 - α) • z + α • K z)^[n + 1] x - (fun z => (1 - α) • z + α • K z)^[n] x‖ ≤ ε := by sorry
end Plasticity.Ext
