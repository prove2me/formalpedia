-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_lemma_4_8
-- name    : PolymerEndpoint.Atomic.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:37:26.565608+00:00
-- url     : https://prove2.me/theorems/d86ce59f-625b-4680-8faa-e0a433dc75c6
-- title:
--   Lemma 4.8 — $\sum_{i<n}\mathcal R(\mathcal T^i\delta_{f_0})\ge\mathbb E\log Z_n$, with equality iff $f_0=\mathbf 1$
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$. For a partitioned subprobability measure $f_0\in\mathcal S$ write $\delta_{f_0}$ for the unit mass at $f_0$, $\mathcal T$ for the update map lifted to probability measures on $\mathcal S$, and $\mathcal R$ for the energy functional (4.6). For every $f_0\in\mathcal S$ and every $n\geq1$,
--
--   $$
--   \sum_{i=0}^{n-1}\mathcal R(\mathcal T^i\delta_{f_0})\geq\mathbb E\log Z_n,
--   $$
--
--   and equality holds if and only if $f_0=\mathbf 1$, the class of the functions that put mass $1$ on a single point.
--
--   This is the key inequality behind the upper bound of Theorem 4.7.
--
--   **Formalization Note** "$f_0=\mathbf 1$ in $\mathcal S$" is encoded as "$f_0(u)=1$ for some cell $u$" (p. 35, via Proposition 2.4), not as equality with one particular representative. $\mathbb E\log Z_n$ is computed on the canonical product environment. The paper's standing assumption $\beta>0$ (§1.1) is kept: at $\beta=0$ both sides vanish for every $f_0$ and the equality case fails.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 35, Lemma 4.8

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem lemma_4_8 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    (f₀ : PSM d) (n : ℕ) (hn : 1 ≤ n) :
    (∫ Y, Real.log (Z (fun u (Y : Cell d → ℝ) => Y u) β n Y) ∂(envLaw (d := d) 𝔏)) ≤
        ∑ i ∈ Finset.range n, RR 𝔏 β ((Tlift 𝔏 β)^[i] (Measure.dirac f₀)) ∧
    ((∫ Y, Real.log (Z (fun u (Y : Cell d → ℝ) => Y u) β n Y) ∂(envLaw (d := d) 𝔏)) =
        ∑ i ∈ Finset.range n, RR 𝔏 β ((Tlift 𝔏 β)^[i] (Measure.dirac f₀)) ↔
      ∃ u : Cell d, f₀.toFun u = 1) := by sorry

end PolymerEndpoint.Atomic
