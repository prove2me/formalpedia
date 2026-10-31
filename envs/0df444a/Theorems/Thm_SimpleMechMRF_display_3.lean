-- Prove2me | Theorems.Thm_SimpleMechMRF_display_3
-- name    : SimpleMechMRF.display_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:07.341607+00:00
-- url     : https://prove2.me/theorems/535cc495-b7e9-4c9f-a375-659e6a092cdb
-- title:
--   Display (3), p.31 — $\Pr[C\ge\mathbb E[C]/2]\ge\frac14\cdot\frac{1}{1+\mathrm{Var}[C]/\mathbb E[C]^2}\ge\frac{1}{4(e^{4\Delta}+2r^2/\mathbb E[C]^2)}$
-- statement:
--   Let the type distribution $D$ be represented by a Markov random field with maximum weighted degree $\Delta$, $r=\mathrm{SRev}$, $C=\sum_i t_i\,\mathbb 1[t_i\le r]$, and suppose $\mathbb E[C]>0$. Then
--
--   $$
--   \Pr\Big[C\ge\frac{\mathbb E[C]}{2}\Big]\;\ge\;\frac14\cdot\frac{1}{1+\mathrm{Var}[C]/\mathbb E[C]^2}\;\ge\;\frac{1}{4\big(e^{4\Delta}+2r^2/\mathbb E[C]^2\big)} .
--   $$
--
--   The first inequality is the Paley–Zygmund inequality at $\theta=1/2$, the second is Lemma 7. When $\mathbb E[C]>\sqrt2\,r$ the right side is at least $1/(4(e^{4\Delta}+1))$, so the grand bundle priced at $\mathbb E[C]/2$ sells with probability bounded below.
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: SRev = r = Σ_i r_i, r_i the revenue of Myerson's auction for item i → r_i = sup_{p∈ℝ} p · Pr[t_i ≥ p]; reason: for one item Myerson's optimal revenue is the best posted price; the supremum is the same with Pr[t_i > p]
--   - encoding: display (3), with the ratios Var[C]/E[C]² and r²/E[C]² → the hypothesis E[C] > 0; reason: the ratios are undefined at E[C] = 0; the proof uses (3) only when E[C] > √2·r ≥ 0
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, proof of Theorem 2, display (3), p.31 (PDF 32)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_MRF
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Display (3) in the proof of Theorem 2** (Cai & Oikonomou, *On Simple Mechanisms for
Dependent Items*, arXiv:2106.10814v2, p. 31, PDF 32). Let the type distribution `D` be the law of
an MRF `G` with maximum weighted degree `Δ`, `r = SRev`, `C = Σᵢ tᵢ · 1[tᵢ ≤ r]`, and suppose
`E[C] > 0`. Then
`Pr[C ≥ E[C]/2] ≥ (1/4) · 1/(1 + Var[C]/E[C]²) ≥ 1/(4 (e^{4Δ} + 2r²/E[C]²))`.

**Formalization Note.** The hypothesis `E[C] > 0` makes the ratios defined; the proof uses (3)
only when `E[C] > √2 r ≥ 0`. `Var[C] = E[C²] − E[C]²`. -/
theorem display_3 {n : ℕ} (G : MRF n) (hC : 0 < G.law.expect (truncSum (srev G.law))) :
    1 / 4 * (1 / (1 + (G.law.expect (fun t => truncSum (srev G.law) t ^ 2) -
          G.law.expect (truncSum (srev G.law)) ^ 2) / G.law.expect (truncSum (srev G.law)) ^ 2)) ≤
        G.law.prob {t | G.law.expect (truncSum (srev G.law)) / 2 ≤ truncSum (srev G.law) t} ∧
    1 / (4 * (Real.exp (4 * G.maxWeightedDegree) +
          2 * srev G.law ^ 2 / G.law.expect (truncSum (srev G.law)) ^ 2)) ≤
      1 / 4 * (1 / (1 + (G.law.expect (fun t => truncSum (srev G.law) t ^ 2) -
          G.law.expect (truncSum (srev G.law)) ^ 2) / G.law.expect (truncSum (srev G.law)) ^ 2)) := by sorry

end SimpleMechMRF
