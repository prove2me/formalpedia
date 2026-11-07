-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_4_6
-- name    : PackingLPAccel.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:33.07596+00:00
-- url     : https://prove2.me/theorems/d82caa16-cd0c-4125-8126-126b004ee94b
-- title:
--   Lemma 4.6 — correctness and cost of Algorithm 1
-- statement:
--   For an instance of Problem 4.4 and $\kappa>0$, Algorithm 1 either returns $y\in[0,u]$ with
--
--   $$G(y)\ge\frac34\kappa,$$
--
--   or it returns FAIL, in which case $G(z)\le514\kappa$ for all $z\in[0,u]$, hence $G^*=O(\kappa)$.
--
--   Moreover one program, with no oracle, computes this outcome in work $\widetilde O(pN_{\mathrm{reg}}\log\Lambda)$ and depth $\widetilde O(p\log\Lambda)$, where $N_{\mathrm{reg}}=D+m^{(2)}+m^{(p)}+\mathrm{nnz}(B^{(2)})+\mathrm{nnz}(B^{(p)})$.
--
--   This is the test of a candidate value, which the regression solver runs at a geometric sequence of values of $\kappa$.
--
--   Differences from the source:
--   - generalization: G* = O(κ) → G(z) ≤ 514κ on [0,u]; reason: the constant of the proof: 2 + 32P − P²/2 ≤ 514
--   - generalization: D variables → any finite index type in the correctness part; reason: Fin D is such a type
--   - encoding: "either returns y … or returns FAIL" → alg1 : Option; register p[0] = 1 or 0 at the end of the program; reason: a flag for the machine-level outcome
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(N_reg + p)^K with C, K after the program, before the instance; reason: polylog in the dimensions and exponents, p.8
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 4.6, p.16 (pdf 17); constant from p.17 (pdf 18)

import Mathlib
import Definitions.Def_PackingLPAccel_Regression

namespace PackingLPAccel

/-- **Lemma 4.6** (manuscript sha256 1dac7711…, p.16). Correctness: the page's `G* = O(κ)` has the explicit
constant `514` of its proof (`2 + 32P - P²/2 ≤ 514`). Cost: a program computes `alg1`, with `p[0] = 1` and the vector in the
output block on a return, and `p[0] = 0` on FAIL, within `Õ(p N_reg log Λ)` work and `Õ(p log Λ)` depth. -/
theorem lemma_4_6 :
    (∀ {ι : Type} [Fintype ι] {m₂ mₚ : ℕ} (R : RegInstance ι m₂ mₚ) (_ : R.IsValid) (κ : ℝ)
        (_ : 0 < κ),
      (∀ y, R.alg1 κ = some y → R.InBox y ∧ (3 / 4) * κ ≤ R.G y) ∧
      (R.alg1 κ = none → ∀ z, R.InBox z → R.G z ≤ 514 * κ)) ∧
    (∃ P : Stmt, ∃ C K : ℕ,
      ∀ (D m₂ mₚ : ℕ) (_ : 1 ≤ D) (R : RegInstance (Fin D) m₂ mₚ) (_ : R.IsValid) (κ : ℝ)
        (_ : 0 < κ) (N₂ Nₚ : ℕ) (e₂ : Fin N₂ → Fin m₂ × Fin D) (eₚ : Fin Nₚ → Fin mₚ × Fin D)
        (_ : IsNonzeroEnum R.B₂ e₂) (_ : IsNonzeroEnum R.Bₚ eₚ),
      ∃ (s' : State) (w d : ℕ), Eval noOracle P (regInit κ R e₂ eₚ) s' w d ∧
        ((∃ y, R.alg1 κ = some y ∧ s'.p 0 = 1 ∧ regOutput D N₂ Nₚ s' = y) ∨
          (R.alg1 κ = none ∧ s'.p 0 = 0)) ∧
        (w : ℝ) ≤ C * R.p * nReg D m₂ mₚ N₂ Nₚ * Real.log (R.alg1Lam κ) *
          (lg (nReg D m₂ mₚ N₂ Nₚ + R.p) : ℝ) ^ K ∧
        (d : ℝ) ≤ C * R.p * Real.log (R.alg1Lam κ) *
          (lg (nReg D m₂ mₚ N₂ Nₚ + R.p) : ℝ) ^ K) := by sorry

end PackingLPAccel
