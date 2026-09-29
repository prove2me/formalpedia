-- Prove2me | Theorems.Thm_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd
-- name    : ValuationSubring.mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cbb240b5-1308-5542-9eb2-b6d5970c6ead
-- title:
--   Membership in a valuation ring centred on a prime varpi
-- statement:
--   Let $K$ be a field and $S \subseteq K$ a subring whose underlying ring is Noetherian. Let $\varpi \in S$ be a prime element, and let $O \subseteq K$ be a valuation subring of $K$ such that every element of $S$, viewed in $K$, lies in $O$. Assume that $O$ is centred on $(\varpi)$ in the following sense: for each $s \in S$, the element $s$, regarded as an element of $O$, lies in the maximal ideal of the local ring $O$ if and only if $\varpi \mid s$ in $S$. The conclusion is that for every $f \in K$ which admits a presentation as a fraction of elements of $S$, that is, for which there exist $g, h \in S$ with $h \neq 0$ in $K$ and $f \cdot h = g$, one has the equivalence: $f \in O$ if and only if there exist $g', h' \in S$ with $\varpi \nmid h'$ in $S$ and $f \cdot h' = g'$ in $K$. In other words, on the fraction field of $S$ inside $K$, the valuation subring $O$ cuts out exactly the elements writable with denominator prime to $\varpi$.
--
--   This identifies a valuation subring centred on a prime element $\varpi$ of a Noetherian subring $S$ with the localisation $S_{(\varpi)}$, as far as elements of $K$ that are fractions of elements of $S$ are concerned. It is used in the analysis of stalks at smooth points in the regular prolongation material, where integrality over a valuation ring must be converted into a denominator condition modulo $\varpi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ValuationSubring.mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd
    {K : Type*} [Field K] (S : Subring K) [IsNoetherianRing ↥S] (ϖ : ↥S) (hϖ : Prime ϖ)
    (O : ValuationSubring K) (hSO : ∀ s : ↥S, (s : K) ∈ O)
    (hcen : ∀ s : ↥S, (⟨(s : K), hSO s⟩ : ↥O) ∈ maximalIdeal ↥O ↔ ϖ ∣ s) :
    ∀ f : K, (∃ g h : ↥S, (h : K) ≠ 0 ∧ f * (h : K) = (g : K)) →
      (f ∈ O ↔ ∃ g h : ↥S, ¬ (ϖ ∣ h) ∧ f * (h : K) = (g : K)) := by sorry
