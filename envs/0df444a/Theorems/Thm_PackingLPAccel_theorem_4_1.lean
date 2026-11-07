-- Prove2me | Theorems.Thm_PackingLPAccel_theorem_4_1
-- name    : PackingLPAccel.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:07.112228+00:00
-- url     : https://prove2.me/theorems/4dca8deb-9f43-418a-b164-3e692f7bd6a7
-- title:
--   Theorem 4.1 — the parallel residual solver
-- statement:
--   There is an absolute $c_0>0$ and one program such that the following holds for all constants $b,c$. Let $R$ be an instance of Problem 1.3 with $\chi_j$ being $L_j$-Lipschitz and $u_j,L_j,v^{(2)}_i,v^{(p)}_i,\phi_{ij}(A_{ij}t)\le\exp(\mathsf{lg}(m+n)^b)$, $p\le\mathsf{lg}(m+n)^b$, and let $\varepsilon\in(0,1)$ with $\varepsilon^{-1}\le(m+n)^c$. Given the numeric data in sparse form and a value oracle for all $\chi_j(\Delta_j)$ and all $\phi_{ij}(A_{ij}\Delta_j)$ with $A_{ij}\ne0$, the program returns a feasible $\hat\Delta$ with
--
--   $$-F(\hat\Delta)\ge c_0(-F(\Delta'))-\varepsilon\qquad\text{for all feasible }\Delta',$$
--
--   with $\widetilde O(1)$ oracle calls, depth $\widetilde O(p)$ and work $\widetilde O(pN_{\mathrm{res}})$. With each call costing $\widetilde O(1)$ depth and $\widetilde O(N_{\mathrm{res}})$ time this gives the printed bounds.
--
--   This solver is the new ingredient of the paper: a residual step in polylogarithmic depth.
--
--   Differences from the source:
--   - generalization: Assumption 3.6 with decomposability and ∥A∥_∞ ≤ poly(m,n) → no decomposability, no bound on ∥A∥_∞; reason: the proof on pp.13–18 uses only the numeric bounds
--   - reading: an oracle returns the values in Õ(1) depth and Õ(N_res) time → the oracle costs (1,1) per call and calls are counted; reason: the printed bound is Õ(1) calls at the printed cost
--   - reading: ψ_j + ∑_i c_{i,j} is L_j-Lipschitz; L_j not listed as input → χ_j is L_j-Lipschitz on I_j, with L_j as an input; reason: the grid of p.14 needs L_j, and χ_j carries the argument A_ij t_j
--   - encoding: −F(∆̂) ≥ Ω(OPT_res) − ε → ∃ c₀ > 0 first, with c₀(−F(∆')) − ε ≤ −F(∆̂) for all feasible ∆'; reason: the meaning of Ω, without a real sSup
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(·)^K with lg(s) = ⌊log₂ s⌋+1 and C, K after the program, before the instance; reason: the meaning of Õ on p.1 and p.8
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Theorem 4.1, p.13 (pdf 14); Assumption 3.6, p.12 (pdf 13)

import Mathlib
import Definitions.Def_PackingLPAccel_Residual

namespace PackingLPAccel

/-- **Theorem 4.1** (manuscript sha256 1dac7711…, p.13). The functions are reachable only through the value oracle, which
costs `(1, 1)` per call: with each call at `(Õ(1), Õ(N_res))` this gives the printed bounds. `L_j` is an input, since the
grid needs it (p.14). `c₀` is absolute and chosen first. Decomposability and `∥A∥_∞ ≤ poly` of Assumption 3.6 are not
required: the proof uses only the numeric bounds. -/
theorem theorem_4_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ P : Stmt, ∀ b c : ℕ, ∃ C K : ℕ,
      ∀ (m n : ℕ) (R : ResidualInstance m n) (_ : R.IsValid) (L : Fin n → ℝ)
        (_ : R.IsQuasiPolyBounded L b) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
        (_ : ε⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c)
        (N : ℕ) (e : Fin N → Fin m × Fin n) (_ : IsNonzeroEnum R.A e)
        (O : OracleModel) (_ : R.IsValueOracle e O),
      ∃ (s' : State) (w d : ℕ), Eval O P (R.resInit ε L e) s' w d ∧
        R.InBox (ResidualInstance.resOutput m n N s') ∧
        (∀ Δ', R.InBox Δ' →
          c₀ * (-R.F Δ') - ε ≤ -R.F (ResidualInstance.resOutput m n N s')) ∧
        (s'.calls : ℝ) ≤ C * (lg (m + n) : ℝ) ^ K ∧
        (d : ℝ) ≤ C * R.p * (lg (m + n) : ℝ) ^ K ∧
        (w : ℝ) ≤ C * R.p * ((m + n + N : ℕ) : ℝ) * (lg (m + n) : ℝ) ^ K := by sorry

end PackingLPAccel
