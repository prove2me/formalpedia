-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_cat_jointProbabilities
-- name    : QAlgorithms.Papers.Independent.Support50.P40.cat_jointProbabilities
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:06:25.894561+00:00
-- url     : https://prove2.me/theorems/d35e0b31-acc1-45a4-bcc3-f8117d3c054c
-- title:
--   Closed cat-code joint probabilities and multiplicities
-- statement:
--   Let $p=m+1\ge1$ and let $f\in[0,1]$, $g=(1-f)/3$. Encode with the ordinary cat code $|b\rangle\mapsto|b\rangle^{\otimes p}$ and decode by the CNOT network of Fig. 7. Fix one syndrome string $i$ of length $m$ with Hamming weight $r$. Let $b_{B,r}$ be its joint probability with residual Bell outcome $B$, rather than a conditional probability or the sum over all syndromes of weight $r$.
--
--   The four masses are
--
--   $$
--   b_{\Psi^+,r}=b_{\Psi^-,r}=2^{p-r-1}g^{p-r}(f+g)^r,
--   $$
--   $$
--   b_{\Phi^\pm,r}=\begin{cases}
--   ((f+g)^p\pm(f-g)^p)/2,&r=0,\\
--   2^{r-1}g^r(f+g)^{p-r},&r>0.
--   \end{cases}
--   $$
--
--   There are exactly $\binom mr$ syndromes of weight $r$, for $0\le r\le m$. Consequently, writing $a_r=\sum_B b_{B,r}$, the exact signed yield is
--
--   $$
--   q_p(f)=\frac1p\left[1+\sum_{r=0}^m\binom mr\left(-a_r\log_2a_r+\sum_B b_{B,r}\log_2b_{B,r}\right)\right].
--   $$
--
--   All zero-log terms are zero. The definition uses the independent physical Pauli law and the actual decoder's residual label, so these formulas identify those probabilities. At $p=1$ the empty syndrome gives masses $f,g,g,g$ and the hashing yield.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 18, Section V.A, Eqs. (36)-(39): closed-form cat-code joint probabilities

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF pp.17--18, Eqs.(36)--(39): the four joint masses for ONE specified
syndrome of weight r. Multiplicity is absent here; summing all syndromes
of that weight introduces `choose(m,r)`. Block size is p=m+1, including p=1. -/
theorem cat_jointProbabilities (m : ℕ) (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (i : Qubits m) :
    let p := m + 1
    let r := hammingWeight i
    let g := noiseG f
    catJoint m f i .X = (2 : ℝ) ^ (p - r - 1) * g ^ (p - r) * (f + g) ^ r ∧
    catJoint m f i .Y = (2 : ℝ) ^ (p - r - 1) * g ^ (p - r) * (f + g) ^ r ∧
    catJoint m f i .I = (if r = 0 then ((f + g) ^ p + (f - g) ^ p) / 2
      else (2 : ℝ) ^ (r - 1) * g ^ r * (f + g) ^ (p - r)) ∧
    catJoint m f i .Z = (if r = 0 then ((f + g) ^ p - (f - g) ^ p) / 2
      else (2 : ℝ) ^ (r - 1) * g ^ r * (f + g) ^ (p - r)) ∧
    (∀ t : ℕ, t ≤ m →
      (Finset.univ.filter (fun s : Qubits m => hammingWeight s = t)).card = Nat.choose m t) ∧
    catYield m f =
      (1 + ∑ t ∈ Finset.range (m + 1), (Nat.choose m t : ℝ) *
        (let a := ∑ j : Pauli, catClosedMass m f t j;
         -a * Real.logb 2 a + ∑ j : Pauli,
           catClosedMass m f t j * Real.logb 2 (catClosedMass m f t j))) / (m + 1) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
