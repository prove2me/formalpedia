-- Prove2me | Theorems.Thm_SimpleMechMRF_lemma_9_cdw
-- name    : SimpleMechMRF.lemma_9_cdw
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:14:58.650265+00:00
-- url     : https://prove2.me/theorems/806f091a-5764-4832-b702-712fe71eaa8d
-- title:
--   Lemma 9 of [14] as used in the proof of Lemma 7, p.30 — $\sum_i\mathbb E[C_i^2]\le 2r^2$
-- statement:
--   Let $D$ be a finite distribution of nonnegative item values, $r=\mathrm{SRev}=\sum_i r_i$ with $r_i=\sup_p p\cdot\Pr[t_i\ge p]$, and $C_i=t_i\cdot\mathbb 1[t_i\le r]$. Then
--
--   $$
--   \sum_{i\in[n]}\mathbb E\big[C_i^2\big]\;\le\;2r^2 .
--   $$
--
--   The bound uses only the marginals of $D$; in the paper it is the variance part of the estimate $\mathrm{Var}[C]\le 2r^2+(e^{4\Delta}-1)\mathbb E[C]^2$ of Lemma 7, quoted from Cai, Devanur and Weinberg [14].
--
--   Differences from the source:
--   - reading: item values t_i of unspecified sign (Def 1: 'interpret ti as the value of item i') → values in ℝ≥0; reason: the proofs use t_i ≥ 0 throughout (Lemma 22 drops π_i ≤ 1 against t_i, Lemma 7 uses c_i c_j ≥ 0, Theorem 2 uses C ≤ Σ t_i); item values are nonnegative in this literature
--   - reading: alphabets Σ_v / type space T of unspecified cardinality → finite alphabets (Finset), finite support; reason: Def 4 takes a max over all configurations and every sum of the paper ranges over a finite T; the duality benchmark [14] is for finite type spaces
--   - encoding: SRev = r = Σ_i r_i, r_i the revenue of Myerson's auction for item i → r_i = sup_{p∈ℝ} p · Pr[t_i ≥ p]; reason: for one item Myerson's optimal revenue is the best posted price; the supremum is the same with Pr[t_i > p]
--   - generalization: D the MRF of Lemma 7 → any finite distribution of nonnegative item values; reason: the bound depends only on the marginals (E[C_i²] ≤ 2r·r_i from Pr[t_i ≥ x] ≤ r_i/x); specializes to the MRF
-- source:
--   Cai & Oikonomou, On Simple Mechanisms for Dependent Items, arXiv:2106.10814v2, proof of Lemma 7, p.30 (PDF 31): 'Using Lemma 9 from [14], we can bound Σ_{i∈[n]} E[C_i^2] by 2r^2'

import Mathlib
import Definitions.Def_SimpleMechMRF_TypeDist
import Definitions.Def_SimpleMechMRF_MRF
import Definitions.Def_SimpleMechMRF_Mechanism
import Definitions.Def_SimpleMechMRF_Benchmark

open scoped NNReal

namespace SimpleMechMRF

/-- **Lemma 9 of [14] as used in the proof of Lemma 7** (Cai & Oikonomou, *On Simple
Mechanisms for Dependent Items*, arXiv:2106.10814v2, proof of Lemma 7, p. 30, PDF 31: "Using
Lemma 9 from [14], we can bound Σ_{i∈[n]} E[Cᵢ²] by 2r²"). For any finite distribution `D` of
nonnegative item values, with `r = SRev = Σᵢ rᵢ` and `Cᵢ = tᵢ · 1[tᵢ ≤ r]`,
`Σᵢ E[Cᵢ²] ≤ 2r²`.

**Formalization Note.** The paper uses it for an MRF; it is stated for every finite
distribution of nonnegative values (it uses only the marginals), which specializes to the
paper's. -/
theorem lemma_9_cdw {n : ℕ} (D : TypeDist n) :
    ∑ i, D.expect (fun t => truncVal (srev D) i t ^ 2) ≤ 2 * srev D ^ 2 := by sorry

end SimpleMechMRF
