-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_codewordState_identification_lower_bound
-- name    : QAlgorithms.Arunachalam.codewordState_identification_lower_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:56:47.955921+00:00
-- url     : https://prove2.me/theorems/ab2e3733-e65b-40c5-a446-ffff55e1e111
-- title:
--   Identifying a codeword state needs Ω(k) copies
-- statement:
--   For a matrix $M\in\mathbb F_2^{n\times k}$ of rank $k$ (the generator matrix of an $[n,k,d]_2$ linear code) and $x\in\{0,1\}^k$ define the codeword state
--
--   $$
--   |\psi_x\rangle=\frac{1}{\sqrt n}\sum_{i\in[n]}|i,(Mx)_i\rangle .
--   $$
--
--   For every rate $c_1>0$ there is a constant $c_0>0$ such that the following holds for all $n,k$ and all rank-$k$ matrices $M\in\mathbb F_2^{n\times k}$ with $k\ge c_1 n$: if a measurement (POVM $\{N_y\}_{y\in\{0,1\}^k}$) on $T$ copies identifies $x$ from $|\psi_x\rangle^{\otimes T}$, for $x$ drawn uniformly from $\{0,1\}^k$, with average success probability
--
--   $$
--   \frac{1}{2^k}\sum_{x\in\{0,1\}^k}\operatorname{Tr}\!\big(N_x\,|\psi_x\rangle\langle\psi_x|^{\otimes T}\big)\ \ge\ \frac45,
--   $$
--
--   then $T\ge c_0\,k$.
--
--   This improves the Holevo-type bound $\Omega(k/\log n)$ to the optimal $\Omega(k)$ for constant-rate codes, showing that codeword fingerprint states cannot be identified from few copies.
--
--   **Formalization Note** "$k=\Omega(n)$" is read as a fixed rate $k\ge c_1 n$, and the constant of $\Omega(k)$ may depend on $c_1$ only. Identifying the state means outputting $x$, which is equivalent since $x\mapsto Mx$ is injective for rank $k$. The code distance $d$ plays no role and is not a hypothesis.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 182, Theorem 7.6.2. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning






/-- Arunachalam p.182, Theorem 7.6.2: let `E = {|ψ_x⟩ = (1/√n) ∑_{i ∈ [n]} |i, (Mx)_i⟩ :
x ∈ {0,1}^k}`, where `M ∈ F₂^{n×k}` is the (rank-`k`) generator matrix of an `[n, k, d]₂` linear
code with `k = Ω(n)`. Then `Ω(k)` copies of an unknown state from `E` (drawn uniformly at random)
are necessary to identify that state with probability at least `4/5`.

`k = Ω(n)` is read as a fixed rate: `k ≥ c₁ n`; the constant `c₀` of `Ω(k)` depends only on `c₁`.
Identifying the state is outputting `x` (rank `k` makes `x ↦ Mx` injective); the measurement is
any POVM on the `T` copies, and success is averaged over the uniform prior. The code distance
plays no role in the statement and is not a binder. -/
theorem codewordState_identification_lower_bound :
    ∀ c₁ : ℝ, 0 < c₁ → ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (n k : ℕ) (M : Matrix (Fin n) (Fin k) (ZMod 2)), M.rank = k → c₁ * (n : ℝ) ≤ (k : ℝ) →
        ∀ (T : ℕ) (N : (Fin k → ZMod 2) →
            Matrix (Fin T → Fin n × Bool) (Fin T → Fin n × Bool) ℂ),
          IsPOVM N →
          ensembleSuccess (fun _ : Fin k → ZMod 2 => ((2 : ℝ) ^ k)⁻¹)
              (fun x => tensorPow T (exampleState (codeConcept M x) (uniformDist (Fin n)))) N ≥
            4 / 5 →
          c₀ * (k : ℝ) ≤ (T : ℝ) := by
  sorry

end QAlgorithms.Arunachalam
