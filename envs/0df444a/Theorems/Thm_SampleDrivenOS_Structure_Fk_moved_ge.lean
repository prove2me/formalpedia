-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_Fk_moved_ge
-- name    : SampleDrivenOS.Structure.Fk_moved_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:42.323021+00:00
-- url     : https://prove2.me/theorems/55baa163-38da-4cbc-9dc5-0cb7066daf80
-- title:
--   Proof of Theorem 2, p. 9 — one mass-moving step does not decrease $F_k$: $F_k(q_{n-1})\le F_k(q_n)$
-- statement:
--   In the setting of the mass-moving step: let $0\le p<1$, let $q$ be feasible for CLP$_p$, let thresholds $t_\ell\in[p,1]$ with $t_\ell>0$ ($\ell\ge1$) satisfy $\int_p^1 q(t,\ell)\,dt=\int_{t_\ell}^1 G_q(t)\,dt$ with $G_q(t)=\frac1t\bigl(1-\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau\bigr)$, and let $q'(t,\ell)=G_q(t)$ for $t\ge t_\ell$ and $0$ otherwise. Then
--   $$F_k(q)\le F_k(q')\qquad\text{for all }k\ge1,$$
--   where $F_k(q)=\sum_{\ell=1}^{k}\int_p^1 q(t,\ell)\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell}\,dt$.
--
--   Together with the previous milestone this shows that each step of the procedure in the proof of Theorem 2 produces a feasible solution that is at least as good for every $F_k$.
--
--   **Formalization Note** The same hypotheses as the previous milestone (thresholds given with their defining equality, $t_\ell>0$, which only matters at $p=0$).
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 9 (PDF p. 10), proof of Theorem 2, F_k(q_{n−1}) ≤ F_k(q_n)

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SampleDrivenOS.Structure

theorem Fk_moved_ge (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (q : ℝ → ℕ → ℝ)
    (hq : IsFeasible p q) (tl : ℕ → ℝ) (htl : ∀ ℓ : ℕ, 1 ≤ ℓ → tl ℓ ∈ Icc p 1)
    (htl0 : ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < tl ℓ)
    (hmass : ∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ) :
    ∀ k : ℕ, 1 ≤ k → Fk p q k ≤ Fk p (movedSolution p q tl) k := by sorry

end SampleDrivenOS.Structure
