-- Prove2me | Theorems.Thm_SampleDrivenOS_Structure_lemma_18
-- name    : SampleDrivenOS.Structure.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:34.628108+00:00
-- url     : https://prove2.me/theorems/8081008c-ac60-465f-a132-011f4bf6c9c4
-- title:
--   Lemma 18 — $\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^\ell$ is non-increasing in the rank $\ell$
-- statement:
--   Fix an integer $k\ge1$ and $t\in[0,1]$. The negative-binomial term
--   $$\mathrm{nb}_{k,\ell}(t)=\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell}$$
--   is a non-increasing function of the rank $\ell\in\{1,2,\dots\}$: for $1\le\ell\le\ell'$, $\mathrm{nb}_{k,\ell'}(t)\le\mathrm{nb}_{k,\ell}(t)$.
--
--   This is the property that lets the proof of Theorem 2 reorder the components of a solution so that the thresholds $t_\ell$ become non-decreasing in $\ell$ without decreasing any $F_k$.
--
--   **Formalization Note** "Decreasing" is read as non-increasing (at $t=0$ every term is $0$). The statement covers all ranks $\ell\ge1$; for $\ell>k$ the sum is empty and equals $0$, consistent with the paper's remark that the coefficient of $q(t,\ell)$ in $F_k$ is $0$ when $\ell>k$.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 29 (PDF p. 30), Lemma 18

import Mathlib
import Definitions.Def_SampleDrivenOS_Structure_Setting

open MeasureTheory Set

namespace SampleDrivenOS.Structure

theorem lemma_18 (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun ℓ : ℕ => nbTerm k ℓ t) (Ici 1) := by sorry

end SampleDrivenOS.Structure
