-- Prove2me | Theorems.Thm_PackingLPAccel_theorem_4_5
-- name    : PackingLPAccel.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:15.433533+00:00
-- url     : https://prove2.me/theorems/a679cd40-f1db-4535-a9c2-a7ce00192798
-- title:
--   Theorem 4.5 — the parallel regression solver
-- statement:
--   There is an absolute $c_0>0$ and one program with no oracle such that, for every instance of Problem 4.4 with $D\ge1$ and every $\delta\in(0,1)$, it returns $\hat y\in[0,u]$ with
--
--   $$G(\hat y)\ge c_0G(z)-\delta\qquad\text{for all }z\in[0,u],$$
--
--   in depth $\widetilde O(p\mathcal L)$ and work $\widetilde O(pN_{\mathrm{reg}}\mathcal L^2)$, where $\mathcal L=1+\log(1+\delta^{-1}(a^\top u+\|B^{(2)}u\|_2^2+\|B^{(p)}u\|_p^p))$.
--
--   This is the width-independent core of the residual solver, an adaptation of the positive $p$-norm packing algorithm of [JLT20].
--
--   Differences from the source:
--   - encoding: G(ŷ) ≥ Ω(G*) − δ, G* = max G → ∃ c₀ > 0 before the program, with c₀G(z) − δ ≤ G(ŷ) for all z; reason: the meaning of Ω, without a real sSup; the paper's L is written 𝓛
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(N_reg + p)^K with C, K after the program, before the instance; reason: polylog in the dimensions and exponents, p.8; dependence on δ is in 𝓛
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Theorem 4.5, p.15 (pdf 16); proof p.18 (pdf 19)

import Mathlib
import Definitions.Def_PackingLPAccel_Regression

namespace PackingLPAccel

/-- **Theorem 4.5** (manuscript sha256 1dac7711…, p.15). `G* = max G` is written as: `G(ŷ) ≥ c₀ G(z) - δ` for every
`z ∈ [0, u]`, with an absolute `c₀ > 0` chosen before the program. The paper's `L` is `𝓛` here;
`lg` is the polylog base in `N_reg` and `p`. -/
theorem theorem_4_5 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ P : Stmt, ∃ C K : ℕ,
      ∀ (D m₂ mₚ : ℕ) (_ : 1 ≤ D) (R : RegInstance (Fin D) m₂ mₚ) (_ : R.IsValid) (δ : ℝ)
        (_ : 0 < δ) (_ : δ < 1) (N₂ Nₚ : ℕ) (e₂ : Fin N₂ → Fin m₂ × Fin D)
        (eₚ : Fin Nₚ → Fin mₚ × Fin D) (_ : IsNonzeroEnum R.B₂ e₂) (_ : IsNonzeroEnum R.Bₚ eₚ),
      let 𝓛 : ℝ := 1 + Real.log (1 + δ⁻¹ * (R.linTerm R.u + ∑ r, R.row₂ R.u r ^ 2 +
        ∑ r, |R.rowₚ R.u r| ^ R.p))
      ∃ (s' : State) (w d : ℕ), Eval noOracle P (regInit δ R e₂ eₚ) s' w d ∧
        R.InBox (regOutput D N₂ Nₚ s') ∧
        (∀ z, R.InBox z → c₀ * R.G z - δ ≤ R.G (regOutput D N₂ Nₚ s')) ∧
        (d : ℝ) ≤ C * R.p * 𝓛 * (lg (nReg D m₂ mₚ N₂ Nₚ + R.p) : ℝ) ^ K ∧
        (w : ℝ) ≤ C * R.p * nReg D m₂ mₚ N₂ Nₚ * 𝓛 ^ 2 *
          (lg (nReg D m₂ mₚ N₂ Nₚ + R.p) : ℝ) ^ K := by sorry

end PackingLPAccel
