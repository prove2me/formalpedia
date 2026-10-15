-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_eq_8_moved_feasible
-- name    : SampleDrivenOS.Structure.eq_8_moved_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:26.620976+00:00
-- url     : https://prove2.me/theorems/56e22bb3-33c3-446c-9ad7-9aa512e28bd4
-- title:
--   (8), p. 9 — one mass-moving step preserves each component's mass, satisfies (8) and keeps the solution feasible
-- statement:
--   Let $0\le p<1$ and let $q$ be feasible for CLP$_p$. Write $M_q(t)=\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau$ and $G_q(t)=\frac1t\bigl(1-M_q(t)\bigr)$. Suppose that for every rank $\ell\ge1$ a threshold $t_\ell\in[p,1]$ with $t_\ell>0$ is given with
--   $$\int_p^1 q(t,\ell)\,dt=\int_{t_\ell}^1 G_q(t)\,dt ,$$
--   and define the moved solution $q'(t,\ell)=G_q(t)$ if $t\ge t_\ell$ and $q'(t,\ell)=0$ if $t<t_\ell$. Then:
--   1. $q'$ is feasible for CLP$_p$;
--   2. $\int_p^1 q'(t,\ell)\,dt=\int_p^1 q(t,\ell)\,dt$ for every $\ell\ge1$;
--   3. inequality (8) holds:
--   $$\frac1t\Bigl(1-\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau\Bigr)\le\frac1t\Bigl(1-\int_p^t\sum_{s\ge1}q'(\tau,s)\,d\tau\Bigr)\qquad\forall t\in[p,1].$$
--
--   This is one step $q_{n-1}\mapsto q_n$ of the procedure in the proof of Theorem 2: the mass of each component is pushed to the right, as far as the feasibility constraint allows.
--
--   **Formalization Note** The thresholds $t_\ell(n)$ are taken as hypotheses satisfying the defining equality; their existence (an intermediate-value argument) is not posed. The thresholds are required to be positive, $t_\ell>0$; this matters only for $p=0$, where $G_q(t)\sim1/t$ is not integrable near $0$, so the paper's defining equality already forces $t_\ell(n)>0$, while Lean's value $\int_0^1 G_q=0$ for a non-integrable integrand would otherwise admit the spurious choice $t_\ell=0$. At the single point $t=0$ Lean reads $1/0$ as $0$, so (8) there is the trivial $0\le0$. The envelope is computed from the extended-real mass converted to a real number; feasibility of $q'$ (item 1) guarantees that this mass is finite, so (8) is not a junk comparison.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 9 (PDF p. 10), proof of Theorem 2, definition of q_n and eq. (8)

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SampleDrivenOS.Structure

theorem eq_8_moved_feasible (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (q : ℝ → ℕ → ℝ)
    (hq : IsFeasible p q) (tl : ℕ → ℝ) (htl : ∀ ℓ : ℕ, 1 ≤ ℓ → tl ℓ ∈ Icc p 1)
    (htl0 : ∀ ℓ : ℕ, 1 ≤ ℓ → 0 < tl ℓ)
    (hmass : ∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, q τ ℓ = ∫ τ in (tl ℓ)..1, envelope p q τ) :
    IsFeasible p (movedSolution p q tl) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∫ τ in p..1, movedSolution p q tl τ ℓ = ∫ τ in p..1, q τ ℓ) ∧
    (∀ τ ∈ Icc p 1, envelope p q τ ≤ envelope p (movedSolution p q tl) τ) := by sorry

end SampleDrivenOS.Structure
