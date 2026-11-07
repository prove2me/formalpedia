-- Prove2me | Theorems.Thm_UltrametricFit_lemma_12
-- name    : UltrametricFit.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:00.929545+00:00
-- url     : https://prove2.me/theorems/d257711d-8493-4820-8e90-b1a37522ee5e
-- title:
--   Lemma 12, p.10 — the one-sided approximate inverse Jensen inequality on a node
-- statement:
--   Let $d$ be a pseudometric with values in $[0,1]$, $\delta\in(0,1/2)$, and $A$ a node of a $\delta$-merge forest. Let $f:A\to[0,1]$ satisfy $|f(i)-f(j)|\le d(i,j)$ for all $i,j\in A$. Then
--   $$\mathbb E_{i\in A}[\phi(f(i))]\ge(1-2\delta)\,\phi\bigl(\mathbb E_{i\in A}[f(i)]\bigr).$$
--   Since $\phi$ is concave, Jensen's inequality gives the opposite direction with constant $1$. The lemma shows that on a node the inequality can be reversed at the cost of the factor $1-2\delta$.
--
--   Differences from the source:
--   - generalization: a metric $d$ → a pseudometric (zero distances between distinct species are allowed); reason: every metric is a pseudometric, and the paper applies the result to the LP layers $x_\ell$, which it calls technically a pseudometric (p.2)
--   - encoding: $f:A\to[0,1]$ → $f$ a real function on all species, in $[0,1]$ on $A$ and read only on $A$; reason: Lean convention; same instances
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), Lemma 12, p.10

import Mathlib
import Definitions.Def_UltrametricFit_IsMergeNode

namespace UltrametricFit

/-- **Lemma 12**, Charikar, Gao, STOC 2027 submission (manuscript sha256 87af12a2…), p.10:
`E_{i∈A}[φ(f(i))] ≥ (1 − 2δ) · φ(E_{i∈A}[f(i)])` for a node `A` and `f : A → [0, 1]` with
`|f(i) − f(j)| ≤ d(i, j)` on `A`.

**Formalization Note.** `f` is a function on all species, read only on `A`. The hypotheses
`d(·, ·) ∈ [0, 1]` (§4.2, p.9) and `δ ∈ (0, 0.5)` (§3, p.8) are the section's standing ones. -/
theorem lemma_12 {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : IsPseudometric d)
    (hd01 : ∀ i j, d i j ∈ Set.Icc (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (A : Finset (Fin n)) (hA : IsMergeNode d δ A) (f : Fin n → ℝ)
    (hf : ∀ i ∈ A, f i ∈ Set.Icc (0 : ℝ) 1) (hlip : ∀ i ∈ A, ∀ j ∈ A, |f i - f j| ≤ d i j) :
    (1 - 2 * δ) * phi (avgOver f A) ≤ avgOver (fun i => phi (f i)) A := by sorry

end UltrametricFit
