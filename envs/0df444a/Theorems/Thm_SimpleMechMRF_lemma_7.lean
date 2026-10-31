-- Prove2me | Theorems.Thm_SimpleMechMRF_lemma_7
-- name    : SimpleMechMRF.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:15:11.129057+00:00
-- url     : https://prove2.me/theorems/b99a526a-a4ca-408c-bdcd-fca9404cf9a8
-- title:
--   Lemma 7, p.12 — $\mathrm{Cov}[C_i,C_j]\le(e^{4\Delta}-1)\mathbb E[C_i]\mathbb E[C_j]$, $\mathrm{Var}[C]\le 2r^2+(e^{4\Delta}-1)\mathbb E[C]^2$ (corrected: $i\ne j$)
-- statement:
--   Let the type distribution $D$ be represented by a Markov random field with maximum weighted degree $\Delta$, let $r=\mathrm{SRev}$, $C_i=t_i\cdot\mathbb 1[t_i\le r]$ and $C=\sum_i C_i$. Then:
--
--   1. for all items $i\ne j$,
--   $$
--   \mathrm{Cov}[C_i,C_j]\;\le\;\big(e^{4\Delta}-1\big)\,\mathbb E[C_i]\,\mathbb E[C_j];
--   $$
--   2. moreover,
--   $$
--   \mathrm{Var}[C]\;\le\;2r^2+\big(e^{4\Delta}-1\big)\,\mathbb E[C]^2 .
--   $$
--
--   Under independence $\mathrm{Var}[C]\le 2r^2$; the second clause is the MRF replacement, which feeds the Paley–Zygmund step of Theorem 2.
--
--   **Formalization Note** $\mathrm{Cov}[X,Y]=\mathbb E[XY]-\mathbb E[X]\mathbb E[Y]$ and $\mathrm{Var}[X]=\mathbb E[X^2]-\mathbb E[X]^2$.
--
--   Differences from the source:
--   - correction: Cov[C_i, C_j] ≤ (exp(4Δ) − 1) E[C_i] E[C_j] 'for any i, j ∈ [n]' → for i ≠ j; reason: false for i = j: n = 1, no hyperedges (Δ = 0), t_1 uniform on {1, 2}: r = 1, Cov[C_1, C_1] = 1/4 > 0 = (e^0 − 1)E[C_1]²; the proof applies Lemma 2 to (t_i, t_{−i}) and the Var clause uses only i ≠ j
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: SRev = r = Σ_i r_i, r_i the revenue of Myerson's auction for item i → r_i = sup_{p∈ℝ} p · Pr[t_i ≥ p]; reason: for one item Myerson's optimal revenue is the best posted price; the supremum is the same with Pr[t_i > p]
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, Lemma 7, p.12 (PDF 13); proof in Appendix C, p.30 (PDF 31)

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_MRF
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Lemma 7, corrected to `i ≠ j`** (Cai & Oikonomou, *On Simple Mechanisms for Dependent
Items*, arXiv:2106.10814v2, p. 12, PDF 13). Let the type distribution `D` be the law of an MRF
`G` with maximum weighted degree `Δ`, `r = SRev`, `Cᵢ = tᵢ · 1[tᵢ ≤ r]` and `C = Σᵢ Cᵢ`. Then
1. for any items `i ≠ j`, `Cov[Cᵢ, Cⱼ] ≤ (e^{4Δ} − 1) E[Cᵢ] E[Cⱼ]`;
2. `Var[C] ≤ 2r² + (e^{4Δ} − 1) E[C]²`.

**Formalization Note.** The paper states clause 1 "for any i, j ∈ [n]"; it is false for
`i = j` (n = 1, no hyperedges so Δ = 0, t₁ uniform on {1, 2}: r = 1, Var[C₁] = 1/4 > 0), and
the paper's proof and its use need only `i ≠ j`. `Cov[X, Y] = E[XY] − E[X]E[Y]`,
`Var[X] = E[X²] − E[X]²`. -/
theorem lemma_7 {n : ℕ} (G : MRF n) :
    (∀ i j : Fin n, i ≠ j →
      G.law.expect (fun t => truncVal (srev G.law) i t * truncVal (srev G.law) j t) -
          G.law.expect (truncVal (srev G.law) i) * G.law.expect (truncVal (srev G.law) j) ≤
        (Real.exp (4 * G.maxWeightedDegree) - 1) *
          G.law.expect (truncVal (srev G.law) i) * G.law.expect (truncVal (srev G.law) j)) ∧
    G.law.expect (fun t => truncSum (srev G.law) t ^ 2) -
        G.law.expect (truncSum (srev G.law)) ^ 2 ≤
      2 * srev G.law ^ 2 +
        (Real.exp (4 * G.maxWeightedDegree) - 1) * G.law.expect (truncSum (srev G.law)) ^ 2 := by sorry

end SimpleMechMRF
