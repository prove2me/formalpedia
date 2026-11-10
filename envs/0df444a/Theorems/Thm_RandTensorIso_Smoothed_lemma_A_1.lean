-- Prove2me | Theorems.Thm_RandTensorIso_Smoothed_lemma_A_1
-- name    : RandTensorIso.Smoothed.lemma_A_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:39:07.657477+00:00
-- url     : https://prove2.me/theorems/5a4bbfe6-9dc7-4b2a-ba3a-ab5f3ca8a0ce
-- title:
--   Lemma A.1 — Algorithm A recovers the diagonal phases from a $(3\tau/4,5)$-seed, in polynomial time
-- statement:
--   Let $S,S'\in\mathbb Q(i)^{n\times n\times n}$, let $\tau\in(0,1]$ be rational, let $(i_0,j_0)$ be a $(3\tau/4,5)$-seed of $S$, let $\ell$ be an integer with $2^{-\ell}\le10^{-7}$, let $0\le\kappa\le10^{-5}\tau$, and let $\Omega_d=\operatorname{diag}(\omega_d)$, $d\in[3]$, be diagonal unitary matrices with $\|S'-(\Omega_1,\Omega_2,\Omega_3)\curvearrowright S\|_F\le\kappa$. Then Algorithm A outputs $\tilde D_1,\tilde D_2,\tilde D_3$ (not FAIL) with
--   $$\|(\tilde D_1,\tilde D_2,\tilde D_3)\curvearrowright S-S'\|_F\le\kappa\Big(1+\frac{29900\|S\|_F}{\tau}\Big)+5600\|S\|_F\,2^{-\ell}.$$
--   On every input, Algorithm A runs in time polynomial in $n$, $\ell$ and the bit length of $S,S'$.
--
--   In Lean the lemma has two parts: (correctness) **every** run of Algorithm A, with any admissible choice of the rounded phases, satisfies the bound; (time) one program, on every input $(n,S,S',i_0,j_0,\tau,\ell)$ with rational $\tau>0$ and $\ell\ge1$, halts within $C(n+\ell+|S|+|S'|)^C+C$ steps, $|S|$ the bit length, and outputs the output (FAIL, or the three diagonals) of a run of Algorithm A.
--
--   Differences from the source:
--   - encoding: Algorithm A computes z_d(x) 'by Newton's iteration on |c_x|^2, then rounding' with parts in 2^{-ℓ-2}ℤ and |z_d(x) − c_x/|c_x|| ≤ 2^{-ℓ} → AlgAOutputs: the output of any run making admissible choices; the bound is proved for every such run; reason: the paper does not fix the rounding; quantifying over all admissible choices covers every implementation
--   - encoding: On every input, Algorithm A runs in time polynomial in n, ℓ and the bit length of S, S′ → ∃ a FinTM2 program and C such that on every input with rational τ > 0 and ℓ ≥ 1 it halts within C(n + ℓ + |enc S| + |enc S′|)^C + C steps with the encoded output of a run of Algorithm A; reason: the paper names no machine; steps of a fixed Turing machine are the time
--   - encoding: ℓ an integer with 2^{-ℓ} ≤ 10^{-7} → ℓ : ℕ with (1/2)^ℓ ≤ 10^{-7}; reason: the condition forces ℓ ≥ 24
--   - encoding: Ω_d = diag(ω_d) diagonal unitary → ω : Fin 3 → Fin n → ℂ with |ω_d(i)| = 1 and Ω_d = diagonal (ω d); reason: the same matrices
-- source:
--   Chizewer, Everett, Mithal, Qiao, Random tensor isomorphism under orthogonal and unitary actions: Smoothed and average-case analysis, STOC 2027 submission (manuscript sha256 f4a12b77…), p. 60 (PDF 62), Lemma A.1

import Mathlib
import Definitions.Def_RandTensorIso_Smoothed_Tensor
import Definitions.Def_RandTensorIso_Smoothed_Spectral
import Definitions.Def_RandTensorIso_Smoothed_Seed
import Definitions.Def_RandTensorIso_Smoothed_Machine

open Matrix

namespace RandTensorIso.Smoothed

/-- Lemma A.1 (p. 60). Correctness: every run of Algorithm A on `(S, S', (i₀, j₀), τ, ℓ)`, under
the lemma's hypotheses, outputs `D̃_d = diag(z_d)` with
`‖(D̃₁, D̃₂, D̃₃) ↷ S − S'‖_F ≤ κ(1 + 29900‖S‖_F/τ) + 5600‖S‖_F 2^{−ℓ}`.
Running time: one program computes, on every input of Algorithm A, the output of a run of
Algorithm A within a polynomial in `n`, `ℓ` and the bit length of `S, S'`. -/
theorem lemma_A_1 :
    (∀ (n : ℕ) (S S' : GTensor n) (τ : ℚ) (i₀ j₀ : Fin n) (ℓ : ℕ) (κ : ℝ)
        (ω : Fin 3 → Fin n → ℂ),
        0 < τ → τ ≤ 1 →
        IsSeed (GTensor.toC S) (3 * (τ : ℝ) / 4) 5 i₀ j₀ →
        (2 : ℝ)⁻¹ ^ ℓ ≤ 1 / 10 ^ 7 →
        0 ≤ κ → κ ≤ (τ : ℝ) / 10 ^ 5 →
        (∀ d i, ‖ω d i‖ = 1) →
        frob (GTensor.toC S' - act (diagonal (ω 0)) (diagonal (ω 1)) (diagonal (ω 2))
          (GTensor.toC S)) ≤ κ →
        ∀ out, AlgAOutputs S S' i₀ j₀ τ ℓ out →
          ∃ z : Fin 3 → Fin n → GQ, out = some z ∧
            frob (act (diagonal (fun x => GQ.toC (z 0 x))) (diagonal (fun x => GQ.toC (z 1 x)))
              (diagonal (fun x => GQ.toC (z 2 x))) (GTensor.toC S) - GTensor.toC S') ≤
              κ * (1 + 29900 * frob (GTensor.toC S) / τ) +
                5600 * frob (GTensor.toC S) * (2 : ℝ)⁻¹ ^ ℓ) ∧
    (∃ (P : Program) (C : ℕ), ∀ (n : ℕ) (S S' : GTensor n) (i₀ j₀ : Fin n) (τ : ℚ) (ℓ : ℕ),
        0 < τ → 1 ≤ ℓ →
        ∃ (out : Option (Fin 3 → Fin n → GQ)) (T : ℕ),
          AlgAOutputs S S' i₀ j₀ τ ℓ out ∧
          P.HaltsWith (encNat n ++ encGTensor S ++ encGTensor S' ++ encNat i₀ ++ encNat j₀ ++
              encRat τ ++ encNat ℓ)
            (match out with
              | none => [false]
              | some z => true :: ((List.finRange 3).flatMap fun d =>
                  (List.finRange n).flatMap fun x => encGQ (z d x))) T ∧
          T ≤ C * (n + ℓ + (encGTensor S).length + (encGTensor S').length) ^ C + C) := by sorry

end RandTensorIso.Smoothed
