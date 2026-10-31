-- Prove2me | Theorems.Thm_SampleMechDesign_lemma_3_10
-- name    : SampleMechDesign.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:12:11.094682+00:00
-- url     : https://prove2.me/theorems/19edd12c-d1f7-41cb-bcf6-a56c9ef1993c
-- title:
--   Lemma 3.10, p.11 — $\mathrm{Pdim}(\mathcal M)\le 9d\ln(4dt)$ (corrected: affine on arrangement cells)
-- statement:
--   Let $\mathcal M=\{\mathrm{profit}_p:p\in P\}$, $P\subseteq\mathbb R^d$, be a $(d,t)$-delineable class of functions on a set $X$, with $d,t\ge1$. Then
--
--   $$
--   \mathrm{Pdim}(\mathcal M)\le 9d\ln(4dt),
--   $$
--
--   that is, if $z_1,\dots,z_m\in X$ are shattered by $\mathcal M$ with some witnesses, then $m\le 9d\ln(4dt)$. This is the combinatorial half of the main theorem: it turns the piecewise structure in the parameters into a complexity bound on the class.
--
--   Differences from the source:
--   - correction: profit_v linear on every connected component of P \ H (Definition 3.5) → IsDelineable: at most t hyperplanes (a ≠ 0) and one affine function on P ∩ C for every sign-vector cell C, faces included; reason: the printed definition makes the result false. P = ℕ ⊆ ℝ has singleton components, so every class indexed by ℕ is delineable and the class of complements of finite subsets of ℕ has infinite pseudo-dimension. P = ℝ² with profit carried on a hyperplane fails the same way
--   - reading: log in 9d log(4dt) → Real.log, the natural logarithm; reason: the base is not pinned. The display also writes ln, while Lemma A.3 is the natural-log lemma of Shalev-Shwartz and Ben-David. The natural logarithm is the stronger reading and it holds by a face count of the arrangement (paper notes)
--   - generalization: X the vectors of buyer values for bundles → an arbitrary measurable space X; reason: the statement uses only X, D and the profit; the paper's X is one instance
--   - encoding: d and t unrestricted → 1 ≤ d and 1 ≤ t; reason: log(4dt) is undefined otherwise; this only excludes undefined cases
--   - encoding: Pdim(M) ≤ k → every shattered m-tuple has m ≤ k; reason: the published Shatters is Definition 3.6 with b the indicator of the complement of T, a tuple with a repeated point is never shattered, and this form also excludes Pdim = ∞
--   - encoding: a set of t hyperplanes, linear → at most t hyperplanes, affine; reason: adding hyperplanes refines cells, so at most and exactly agree for t ≥ 1; the proof of Lemma 3.10 writes profit = a·p + b
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Lemma 3.10, p.11 (PDF p.11); Definitions 3.6, 3.7, p.10

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_SampleMechDesign_IsDelineable

namespace SampleMechDesign

open FoundationsML.Regression

/-- **Lemma 3.10.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, p.11. A `(d, t)`-delineable
class has pseudo-dimension at most `9 d ln(4 d t)`.

**Formalization Note.** "`Pdim(M) ≤ k`" is written as: every `m`-tuple of valuations shattered by
`profit '' P` has `m ≤ k`, which also excludes `Pdim = ∞`. `log` is the natural logarithm, the
stronger reading. `d, t ≥ 1` exclude `log 0`. `IsDelineable` is the corrected Definition 3.5. -/
theorem lemma_3_10 {X : Type*} {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) {P : Set (Fin d → ℝ)}
    {profit : (Fin d → ℝ) → X → ℝ} (hdel : IsDelineable d t P profit)
    {m : ℕ} (z : Fin m → X) (hz : Shatters (profit '' P) z) :
    (m : ℝ) ≤ 9 * (d : ℝ) * Real.log (4 * (d : ℝ) * (t : ℝ)) := by sorry

end SampleMechDesign
