-- Prove2me | Theorems.Thm_SetMultCost_lemma_7_3
-- name    : SetMultCost.lemma_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:14.049202+00:00
-- url     : https://prove2.me/theorems/2ba92758-22f1-4e19-97ff-7bcc2e1eeb27
-- title:
--   Lemma 7.3 — relative rank of restricted set-multilinear circuits
-- statement:
--   There are absolute constants $c_0>0$ and $n_0$ such that the following holds. Let $\Delta,c\ge1$, $d\ge2$, $n\ge n_0$, and let $M$ be an integer with
--
--   $$\tfrac23M^{F(\Delta+1)-1}\le d\le M^{F(\Delta+1)-1},\qquad M\ge200c^2.$$
--
--   Let $\tilde\alpha=\tilde\alpha_{M,c}$ with $d\le n^{\tilde\alpha}$. Suppose $P$ is set-multilinear of degree $d$, computed by a set-multilinear $\mathbf r$-restricted circuit of product-depth at most $2\Delta$ and size $s$, for $\mathbf r=(c,\infty,c,\infty,\dots)$. Then for every partition $\pi=(\mathcal P,\mathcal N)$ of $[d]$,
--
--   $$\mathrm{relrk}_{n,\tilde\alpha,\pi}(P)\le s\cdot n^{-c_0\,d^{1/(F(\Delta+1)-1)}/c^2}.$$
--
--   This is the upper bound of the rank method, with exponent $F(\Delta+1)-1$ for product-depth $2\Delta$, which is what removes the loss in the escalation step.
--
--   Differences from the source:
--   - generalization: an r-restricted formula → an r-restricted circuit; reason: the input is the circuit of Theorem 3.5, and Lemma 4.2 is for circuits; formulas are an instance
--   - generalization: d ∈ O(log n / log log n) → d ≤ n^α̃; reason: the proof uses only "We have n^α > d" (p.24); the printed range for large n is an instance
--   - reading: n^{−Ω(·)} with c fixed → c₀, n₀ chosen before c and F; reason: the exponent displays c², which only has content if c₀ does not depend on c
--   - generalization: "Fix a positive integer ∆", then Ω, so the constant may depend on Δ → c₀, n₀ chosen before Δ as well; reason: uniform constants specialize to the per-Δ statement; the proof's constant (m ≥ M/(1000c²), relrk ≤ 2s·n^{−m/2}) does not involve Δ
--   - encoding: d growing, "Assume d is large enough" → 2 ≤ d; reason: implied by ⅔·M^{F(∆+1)−1} ≤ d with M ≥ 200c² ≥ 200, so no instance is excluded
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 7.3, p.23

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_IsRestricted
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_Circuit_IsSetMultilinear
import Definitions.Def_SetMultCost_relrk
import Definitions.Def_SetMultCost_fibF
import Definitions.Def_SetMultCost_cfDen
import Definitions.Def_SetMultCost_alphaTildeDigits

universe u

namespace SetMultCost

/-- **Lemma 7.3.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.23: "Fix a positive integer ∆ and c. For all d ∈ O(log n/ log log n), choose
a positive integer M that satisfies 2/3 · M^{F(∆+1)−1} ≤ d ≤ M^{F(∆+1)−1}, and let α̃ = α̃M,c defined at
the beginning of Section 7.2. Assume d is large enough so that M ≥ 200c². Suppose P(x) is a
set-multilinear polynomial of degree-d that can be computed by an r-restricted product-depth-2∆
set-multilinear formula F of size s, for r = (c, ∞, c, ∞, · · · ) ∈ (N ∪ {∞})^{2∆}. Then, for partition
π = (P, N) of [d], we have, relrkn,α̃,π(P) ≤ s · n^{−Ω(d^{1/F(∆+1)−1}/c²)}."

**Formalization Note.** Two generalizations. Circuits in place of the printed "formula", since the input
is the circuit of Theorem 3.5 and Lemma 4.2 is for circuits. And `d ≤ n^α̃` in place of `d ∈ O(log n /
log log n)`, which is what the proof uses it for (p.24, "We have n^α > d"). The constants `c₀, n₀` in
`Ω` are absolute: they are chosen before `Δ`, `c`, `F`. -/
theorem lemma_7_3 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ,
      ∀ (F : Type u) [Field F] (Δ c M d n : ℕ) (α : ℝ), 1 ≤ Δ → 1 ≤ c → 2 ≤ d → n₀ ≤ n →
        (2 : ℝ) / 3 * (M : ℝ) ^ R Δ ≤ (d : ℝ) → d ≤ M ^ R Δ → 200 * c ^ 2 ≤ M →
        IsCFValue (alphaTildeDigits M c) α → (d : ℝ) ≤ (n : ℝ) ^ α →
        ∀ (P : Finset (Fin d)) (Φ : Circuit (Var d (sizeFn P ⌊(n : ℝ) ^ α⌋₊ n)) F),
          Φ.IsRestricted (2 * Δ) (altRestriction c) → Φ.IsSetMultilinear Sigma.fst →
          IsSetMultilinearOn Sigma.fst Finset.univ Φ.value →
          relrk n α P Finset.univ Φ.value ≤
            (Φ.size : ℝ) * (n : ℝ) ^ (-(c₀ * (d : ℝ) ^ (1 / (R Δ : ℝ)) / (c : ℝ) ^ 2)) := by sorry

end SetMultCost
