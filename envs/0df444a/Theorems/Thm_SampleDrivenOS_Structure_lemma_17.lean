-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_lemma_17
-- name    : SampleDrivenOS.Structure.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:29.265609+00:00
-- url     : https://prove2.me/theorems/214b2034-d97d-4d89-a597-4e2a5e6fa70f
-- title:
--   Lemma 17 — $\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^\ell$ is non-decreasing in $t\in[0,1]$
-- statement:
--   Fix integers $k\ge1$ and $1\le\ell\le k$. The negative-binomial term
--   $$\mathrm{nb}_{k,\ell}(t)=\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell}$$
--   is a non-decreasing function of $t$ on $[0,1]$: for $0\le s\le t\le1$, $\mathrm{nb}_{k,\ell}(s)\le\mathrm{nb}_{k,\ell}(t)$.
--
--   The term $\mathrm{nb}_{k,\ell}(t)$ is the coefficient of $q(t,\ell)$ in $F_k(q)$; its monotonicity in $t$ is what makes moving stopping mass to later times weakly increase every $F_k$ in the proof of Theorem 2.
--
--   **Formalization Note** The paper's "increasing" is read as non-decreasing (its proof shows the derivative is $\ge0$). The rank $\ell\ge1$ is implicit in the paper.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 28 (PDF p. 29), Lemma 17

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SampleDrivenOS.Structure

theorem lemma_17 (k ℓ : ℕ) (hk : 1 ≤ k) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k) :
    MonotoneOn (nbTerm k ℓ) (Icc 0 1) := by sorry

end SampleDrivenOS.Structure
