-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_theorem_2_10
-- name    : RandTensorIso.Smoothed.theorem_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:39:19.337865+00:00
-- url     : https://prove2.me/theorems/dc8ed581-8945-4989-99f8-fe8f12e87bd2
-- title:
--   Theorem 2.10 — deciding the unitary orbit approximation problem for gapped tensors whose core has a seed
-- statement:
--   Let $n\ge2$, let $A,B\in\mathbb Q(i)^{n\times n\times n}$, and let $\delta>0$ be a rational such that $G_d(A)$ has simple spectrum with minimum eigenvalue gap at least $\delta$ for every $d\in[3]$, and the core $S_A$ has a $(1/12,5)$-seed. Then for every rational $\varepsilon$ with $0<\varepsilon\le\delta/(10^8\lceil\sqrt n\rceil\|A\|_F^2)$, there is an algorithm that runs in time polynomial in $n$, $\log(1/\varepsilon)$, $\log(1/\delta)$ and the bit length of $A,B$, distinguishing $\operatorname{dist}_{\mathbb C}(A,B)<\varepsilon$ from $\operatorname{dist}_{\mathbb C}(A,B)>\gamma\varepsilon$ for
--   $$\gamma=\frac{10^8\lceil\sqrt n\rceil\|A\|_F^3}{\delta},$$
--   and in the former case outputs a witness $(\hat L,\hat R,\hat T)\in U(n)^3$ with entries in $\mathbb Q(i)$ and $\|(\hat L,\hat R,\hat T)\curvearrowright A-B\|_F\le\gamma\varepsilon$. On every input, every witness it outputs satisfies these conditions, and it outputs NO whenever $\operatorname{dist}_{\mathbb C}(A,B)>\gamma\varepsilon$.
--
--   In Lean: one program with input $(n,A,B,\delta,\varepsilon)$ (Algorithm 3's input) and a constant $C$; under the hypotheses it halts within $C(n+\log^+(1/\varepsilon)+\log^+(1/\delta)+|A|+|B|)^C+C$ steps with a correct output for Problem 1 with this $\gamma$; and on every input with $n\ge2$ and rational $\delta,\varepsilon>0$, every YES output carries a valid witness and the program halts with NO whenever $\operatorname{dist}_{\mathbb C}(A,B)>\gamma\varepsilon$. Here $\log^+=\max(0,\log)$.
--
--   Differences from the source:
--   - reading: for every rational ε … there exists an algorithm (Algorithm 3 takes δ, ε as input) → one program, chosen before n, A, B, δ, ε, that reads (n, A, B, δ, ε); reason: the algorithm of the proof is Algorithm 3, whose input includes δ and ε; the uniform reading is the stronger one
--   - encoding: G_d(A) has simple spectrum with minimum eigenvalue gap at least δ → MinEigGap (A) δ with δ > 0; reason: a gap at least δ > 0 already makes the spectrum simple
--   - encoding: the core S_A has a (1/12, 5)-seed → CoreHasSeed: some HOSVD core of A has a (1/12, 5)-seed; reason: under simple spectra every core has the same moduli |S_A(p)|, so the choice does not matter
--   - encoding: runs in time polynomial in n, log(1/ε), log(1/δ) and the bit length of A, B → halts within C(n + max(0, log(1/ε)) + max(0, log(1/δ)) + |enc A| + |enc B|)^C + C steps of a FinTM2 program; reason: the paper names no machine; a polynomial is bounded by C(·)^C + C, and the positive part only matters when ε or δ exceeds 1
--   - encoding: On every input, every witness it outputs satisfies these conditions, and it outputs NO whenever dist_C(A, B) > γε → for every n ≥ 2 and rational δ, ε > 0 (the algorithm's inputs): every halting YES output has a valid witness, and the program halts with NO when dist_C(A, B) > γε; reason: 'outputs NO' read as halting with NO
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 25 (PDF 27), Theorem 2.10

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_Seed
import Definitions.Def_RandTensorIso_Smoothed_Machine

open Matrix

namespace RandTensorIso.Smoothed

/-- Theorem 2.10 (p. 25). There is one program, run on `(n, A, B, δ, ε)` with
`A, B ∈ ℚ(i)^{n×n×n}` and rationals `δ, ε > 0`, and with `γ = 10 ^ 8⌈√n⌉‖A‖_F³/δ`, such that:
(a) if `n ≥ 2`, the Gram matrices of `A` have minimum eigenvalue gap at least `δ` (hence simple
spectra), the core `S_A` has a `(1/12, 5)`-seed and `0 < ε ≤ δ/(10 ^ 8⌈√n⌉‖A‖_F²)`, then it halts
within a polynomial in `n`, `log(1/ε)`, `log(1/δ)` and the bit length of `A, B`, and its output
solves Problem 1 (YES with a `ℚ(i)` unitary witness within `γε` if `dist_ℂ(A, B) < ε`, NO if
`dist_ℂ(A, B) > γε`);
(b) on every input (with `n ≥ 2`, `δ, ε > 0`), every witness it outputs is unitary with entries in `ℚ(i)` and satisfies
`‖(L̂, R̂, T̂) ↷ A − B‖_F ≤ γε`, and it outputs NO whenever `dist_ℂ(A, B) > γε`. -/
theorem theorem_2_10 :
    ∃ (P : Program) (C : ℕ),
      (∀ (n : ℕ) (A B : GTensor n) (δ ε : ℚ),
        2 ≤ n → 0 < δ →
        MinEigGap (GTensor.toC A) δ →
        CoreHasSeed (GTensor.toC A) (1 / 12) 5 →
        0 < ε → (ε : ℝ) ≤ δ / (10 ^ 8 * ⌈Real.sqrt n⌉₊ * frob (GTensor.toC A) ^ 2) →
        ∃ (out : List Bool) (T : ℕ), P.HaltsWith (alg3Input A B δ ε) out T ∧
          (T : ℝ) ≤ C * ((n : ℝ) + max 0 (Real.log (1 / (ε : ℝ))) + max 0 (Real.log (1 / (δ : ℝ)))
              + (encGTensor A).length + (encGTensor B).length) ^ C + C ∧
          GappedCorrect (GTensor.toC A) (GTensor.toC B) ε
            (10 ^ 8 * ⌈Real.sqrt n⌉₊ * frob (GTensor.toC A) ^ 3 / δ) out) ∧
      (∀ (n : ℕ) (A B : GTensor n) (δ ε : ℚ), 2 ≤ n → 0 < δ → 0 < ε →
        (∀ (out : List Bool) (T : ℕ), P.HaltsWith (alg3Input A B δ ε) out T →
          ∀ L R S : Matrix (Fin n) (Fin n) GQ, out = encYes L R S →
            gqMat L ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ gqMat R ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
            gqMat S ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
            frob (act (gqMat L) (gqMat R) (gqMat S) (GTensor.toC A) - GTensor.toC B) ≤
              10 ^ 8 * ⌈Real.sqrt n⌉₊ * frob (GTensor.toC A) ^ 3 / δ * ε) ∧
        (10 ^ 8 * ⌈Real.sqrt n⌉₊ * frob (GTensor.toC A) ^ 3 / δ * ε <
            distC (GTensor.toC A) (GTensor.toC B) →
          ∃ T : ℕ, P.HaltsWith (alg3Input A B δ ε) encNo T)) := by sorry

end RandTensorIso.Smoothed
