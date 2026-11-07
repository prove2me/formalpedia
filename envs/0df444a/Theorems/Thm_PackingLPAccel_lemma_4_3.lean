-- Prove2me | Theorems.Thm_PackingLPAccel_lemma_4_3
-- name    : PackingLPAccel.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:20.837806+00:00
-- url     : https://prove2.me/theorems/3e664f72-ddab-49e3-938c-6ee94aeef371
-- title:
--   Lemma 4.3 — the piecewise-linear regression instance of a residual problem
-- statement:
--   Let $R$ be an instance of Problem 1.3 with $n\ge1$, $\chi_j$ being $L_j$-Lipschitz on $I_j$, and $\delta>0$, and let $G$ be the objective of the grid instance with box $[0,\ell]$. Every $y\in[0,\ell]$ gives, through $z_j=\sum_ky_{j,k}$ and $\Delta=z^+-z^-$, a feasible update with $-F(\Delta)\ge G(y)$. Moreover
--
--   $$G^*\ge\frac14\mathrm{OPT}_{\mathrm{res}}-\frac12\delta.$$
--
--   Each signed coordinate $s$ has $K_s\le\lceil\log_2(2n(1+\tilde u_sL_s)\delta^{-1})\rceil_++2$ variables, both matrices have $m$ rows, and their entries vanish wherever $A$ does.
--
--   Under the numeric bounds of Assumption 3.6 and $\delta^{-1}\le(m+n)^c$, one program with the value oracle writes the instance in the regression layout within $\widetilde O(1)$ calls and depth and $\widetilde O(N_{\mathrm{res}})$ work, where $N_{\mathrm{res}}=m+n+\mathrm{nnz}(A)$.
--
--   This is the discretization of §4.1: it loses only a constant factor and an additive $\delta/2$.
--
--   Differences from the source:
--   - reading: G* := max G ≥ ¼OPT_res − ½δ → some y ∈ [0,ℓ] has G(y) ≥ ¼(−F(∆')) − ½δ for all feasible ∆'; reason: OPT_res need not be attained under the bare hypotheses; this form implies the printed one
--   - generalization: δ = Θ(ε); the bound Õ(N_res) on sizes → every δ > 0; an explicit bound on K_s and the vanishing of entries; reason: they imply the printed size bound
--   - reading: the instance can be constructed in Õ(1) depth and Õ(N_res) time → one program with the value oracle at cost (1,1) per call, under the numeric bounds of Assumption 3.6 and δ⁻¹ ≤ (m+n)^c, the setting of Theorem 4.1; reason: the printed bound holds in that setting (p.15), and the oracle's cost is charged in Theorem 4.1's hypothesis
--   - encoding: ũ_j = 0 is not discussed → K_s = 0, grid {0}; reason: the p.14 phrase "allowing K_j = 0"
--   - encoding: variable order, the index set of the columns → any bijection Fin D ≃ the grid variables; reason: the page fixes none
--   - reading: "There is a … algorithm", PRAM, the list of p.8 → one program of the language Stmt/Eval (CREW, snapshot parFor, exclusive write), with no log, exp, floor or integer multiplication; reason: the paper names only PRAM and the p.8 list; the list is taken literally, as the non-weaker reading, although the paper's proof evaluates log (p.28)
--   - generalization: the input is A → every enumeration of the nonzero entries, in any order; reason: a fixed order is one such enumeration
--   - encoding: Õ(·) → C·(…)·lg(·)^K with lg(s) = ⌊log₂ s⌋+1 and C, K after the program, before the instance; reason: the meaning of Õ on p.1 and p.8
-- source:
--   Chen, Chen, Graur, Sidford, Accelerated Parallel Algorithms for Packing Linear Programming, STOC 2027 submission (manuscript sha256 1dac7711…), Lemma 4.3, p.14 (pdf 15)

import Mathlib
import Definitions.Def_PackingLPAccel_Residual

namespace PackingLPAccel

/-- **Lemma 4.3** (manuscript sha256 1dac7711…, p.14). `G*` is written as: some `y ∈ [0, ℓ]` has
`G(y) ≥ ¼(-F(∆')) - ½δ` for all feasible `∆'`. Size clause: explicit grid bound, and `B^{(2)}`, `B^{(p)}` vanish wherever `A`
does, with `m` rows by type. Construction clause: under the bounds of Assumption 3.6 and `δ⁻¹ ≤ (m+n)^c`, one program with the value oracle
writes the instance in the regression layout, with its variables in any order. -/
theorem lemma_4_3 :
    (∀ (m n : ℕ) (_ : 0 < n) (R : ResidualInstance m n) (_ : R.IsValid) (L : Fin n → ℝ)
        (_ : R.ChiLipschitz L) (δ : ℝ) (_ : 0 < δ),
      (∀ y, (R.gridInstance L δ).InBox y →
        R.InBoxT (R.yToZ L δ y) ∧ R.InBox (ResidualInstance.zToDelta (R.yToZ L δ y)) ∧
        (R.gridInstance L δ).G y ≤ -R.F (ResidualInstance.zToDelta (R.yToZ L δ y))) ∧
      (∃ y, (R.gridInstance L δ).InBox y ∧
        ∀ Δ', R.InBox Δ' → (1 / 4) * (-R.F Δ') - (1 / 2) * δ ≤ (R.gridInstance L δ).G y) ∧
      (∀ s, R.gridK L δ s ≤
        ⌈Real.logb 2 (2 * n * (1 + R.uT s * Sum.elim L L s) * δ⁻¹)⌉₊ + 2) ∧
      (∀ i (j : Fin n) (s : Fin n ⊕ Fin n) (k : Fin (R.gridK L δ s)),
        s = Sum.inl j ∨ s = Sum.inr j → R.A i j = 0 →
          (R.gridInstance L δ).B₂ i ⟨s, k⟩ = 0 ∧ (R.gridInstance L δ).Bₚ i ⟨s, k⟩ = 0)) ∧
    (∃ P : Stmt, ∀ b c : ℕ, ∃ C K : ℕ,
      ∀ (m n : ℕ) (_ : 0 < n) (R : ResidualInstance m n) (_ : R.IsValid) (L : Fin n → ℝ)
        (_ : R.IsQuasiPolyBounded L b) (δ : ℝ) (_ : 0 < δ) (_ : δ⁻¹ ≤ ((m + n : ℕ) : ℝ) ^ c)
        (N : ℕ) (e : Fin N → Fin m × Fin n) (_ : IsNonzeroEnum R.A e)
        (O : OracleModel) (_ : R.IsValueOracle e O),
      ∃ (s' : State) (w d : ℕ), Eval O P (R.resInit δ L e) s' w d ∧
        (∃ (D N₂ Nₚ : ℕ) (eq : Fin D ≃ R.GridIdx L δ)
            (e₂ : Fin N₂ → Fin m × Fin D) (eₚ : Fin Nₚ → Fin m × Fin D),
          let G : RegInstance (Fin D) m m :=
            { a := fun i => (R.gridInstance L δ).a (eq i)
              u := fun i => (R.gridInstance L δ).u (eq i)
              B₂ := fun r i => (R.gridInstance L δ).B₂ r (eq i)
              Bₚ := fun r i => (R.gridInstance L δ).Bₚ r (eq i)
              p := R.p }
          IsNonzeroEnum G.B₂ e₂ ∧ IsNonzeroEnum G.Bₚ eₚ ∧
            HoldsBlocks s' (regReals δ G e₂ eₚ) (regInts G e₂ eₚ)) ∧
        (s'.calls : ℝ) ≤ C * (lg (m + n) : ℝ) ^ K ∧
        (w : ℝ) ≤ C * ((m + n + N : ℕ) : ℝ) * (lg (m + n) : ℝ) ^ K ∧
        (d : ℝ) ≤ C * (lg (m + n) : ℝ) ^ K) := by sorry

end PackingLPAccel
