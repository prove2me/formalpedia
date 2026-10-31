-- Prove2me | Theorems.Thm_SimpleMechMRF_bundle_bound
-- name    : SimpleMechMRF.bundle_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:02.251341+00:00
-- url     : https://prove2.me/theorems/aafbc941-8e3e-4818-8686-0133b220e20f
-- title:
--   Proof of Theorem 2, p.31 — if $\mathbb E[C]>\sqrt2\,r$ then $8(e^{4\Delta}+1)\cdot\mathrm{BRev}\ge\textsc{Core}$
-- statement:
--   Let the type distribution $D$ be represented by a Markov random field with maximum weighted degree $\Delta$, $r=\mathrm{SRev}$, $C=\sum_i t_i\,\mathbb 1[t_i\le r]$. If $\mathbb E[C]>\sqrt2\cdot r$, then
--
--   $$
--   8\big(e^{4\Delta}+1\big)\cdot\mathrm{BRev}\;\ge\;\textsc{Core},
--   $$
--
--   with $\textsc{Core}=\sum_i\sum_{t_i\le r}f_i(t_i)\,t_i$. This is the "Otherwise" branch of the proof of Theorem 2: selling the grand bundle at price $\textsc{Core}/2$ recovers a $1/(8(e^{4\Delta}+1))$ fraction of the Core.
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: SRev = r = Σ_i r_i, r_i the revenue of Myerson's auction for item i → r_i = sup_{p∈ℝ} p · Pr[t_i ≥ p]; reason: for one item Myerson's optimal revenue is the best posted price; the supremum is the same with Pr[t_i > p]
--   - encoding: BRev, the optimal revenue from selling the grand bundle → sup_{p∈ℝ} p · Pr[Σ_i t_i ≥ p]; reason: selling the grand bundle is posting one price for it; the buyer buys when the bundle's value is at least the price
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, proof of Theorem 2, p.31 (PDF 32): 'Thus 8 (exp(4∆(t)) + 1) · BRev ≥ Core'

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_MRF
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **The bundle bound in the proof of Theorem 2** (Cai & Oikonomou, *On Simple Mechanisms for
Dependent Items*, arXiv:2106.10814v2, p. 31, PDF 32: "Thus 8 (exp(4∆(t)) + 1) · BRev ≥ Core").
Let the type distribution `D` be the law of an MRF `G` with maximum weighted degree `Δ`,
`r = SRev`, `C = Σᵢ tᵢ · 1[tᵢ ≤ r]`. If `E[C] > √2 · r` (the "Otherwise" case of the proof),
then `8 (e^{4Δ} + 1) · BRev ≥ Core`, with `Core` at the cutoff `r`.

**Formalization Note.** `BRev = sup_p p · Pr[Σᵢ tᵢ ≥ p]`. -/
theorem bundle_bound {n : ℕ} (G : MRF n)
    (hC : Real.sqrt 2 * srev G.law < G.law.expect (truncSum (srev G.law))) :
    G.law.core (srev G.law) ≤ 8 * (Real.exp (4 * G.maxWeightedDegree) + 1) * brev G.law := by sorry

end SimpleMechMRF
