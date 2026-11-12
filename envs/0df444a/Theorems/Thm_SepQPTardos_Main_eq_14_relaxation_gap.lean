-- Prove2me | Theorems.Thm_SepQPTardos_Main_eq_14_relaxation_gap
-- name    : SepQPTardos.Main.eq_14_relaxation_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:25.448787+00:00
-- url     : https://prove2.me/theorems/7e92a775-1644-49c1-83a0-4accfa80a361
-- title:
--   §4, eq. (14) — the relaxation gap identity and its consequences
-- statement:
--   Let $A$ be an integer $r\times m$ matrix, $b,c,q$ real with $q\ge0$, and let $(x^*,\pi^*)$ be an optimal primal–dual pair of (1), i.e. a solution of (8); put $\sigma^*=Qx^*+c-A^\top\pi^*$ and $T^*=\{e:\sigma^*_e=0\}$, and let $F\subseteq T^*$. Then for every $x\in P_F(b)$,
--
--   $$\Phi(x)-\Phi(x^*)=\tfrac12\sum_{e\in N}q_e(x_e-x^*_e)^2+\sum_{e\notin F}\sigma^*_ex_e\ \ge\ 0.\tag{14}$$
--
--   Consequently the relaxed minimum equals the original minimum: $x^*$ is an optimum on $P_F(b)$, and every optimum $z$ on $P_F(b)$ has $\Phi(z)=\Phi(x^*)$, $z_N=x^*_N$, and $z_e>0$ for $e\notin F$ implies $e\in T^*$.
--
--   The identity justifies removing the nonnegativity constraints on $F$ and certifies every coordinate the algorithm adds to $F$.
--
--   Differences from the source:
--   - generalization: A ∈ ℤ^{r×m}, rational b, c, q → integer A, real b, c, q; reason: the argument uses no rationality of b, c, q; rational data are a special case
--   - generalization: §4 runs under (7): feasible and finite, 1 ≤ r < m, N ≠ ∅, and after deleting redundant rows of A → none of these assumed; only q ≥ 0, an optimal pair (x*, π*) satisfying (8), and F ⊆ T*; reason: the argument does not use them; an instance satisfying (7) is a special case
--   - encoding: an optimal primal–dual pair (x*, π*) → (x*, π*) satisfying (8); reason: (8) is the paper's certificate of an optimal primal–dual pair
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, STOC 2027 submission #829 (October 2026), §4, eq. (14) and the sentences following it, pp. 7–8

import Mathlib
import Definitions.Def_SepQPTardos_Main_Problem
import Definitions.Def_SepQPTardos_Main_Circuits
import Definitions.Def_SepQPTardos_Main_Analysis

open Matrix

namespace SepQPTardos.Main

/-- §4, eq. (14) (Cui–Li–Miao, STOC 2027 #829, pp. 7–8). Context of §4: `q ≥ 0`, `(x*, π*)` is
an optimal primal–dual pair of (1) (it satisfies (8)), `σ* = Qx* + c − Aᵀπ*`, and `F ⊆ T*`.
For every `x ∈ P_F(b)`,
`Φ(x) − Φ(x*) = ½ ∑_{e∈N} qₑ(xₑ − x*ₑ)² + ∑_{e∉F} σ*ₑ xₑ ≥ 0`.
Hence the relaxed minimum equals the original minimum (`x*` is a relaxed optimum and every
relaxed optimum has value `Φ(x*)`), every relaxed optimum `z` has `z_N = x*_N`, and `zₑ > 0`
for some `e ∉ F` implies `e ∈ T*`. -/
theorem eq_14_relaxation_gap {r m : ℕ} (A : Matrix (Fin r) (Fin m) ℤ) (b : Fin r → ℝ)
    (q c : Fin m → ℝ) (xs : Fin m → ℝ) (πs : Fin r → ℝ) (F : Finset (Fin m))
    (hctx : Sec4Context A b q c xs πs F) :
    (∀ x ∈ PF A b F,
      Phi q c x - Phi q c xs =
          (1 / 2 : ℝ) * ∑ e ∈ Nset q, q e * (x e - xs e) ^ 2 +
            ∑ e ∈ Fᶜ, slack (castMat A) q c xs πs e * x e ∧
      0 ≤ (1 / 2 : ℝ) * ∑ e ∈ Nset q, q e * (x e - xs e) ^ 2 +
            ∑ e ∈ Fᶜ, slack (castMat A) q c xs πs e * x e) ∧
    IsMinimizer (PF A b F) (Phi q c) xs ∧
    ∀ z, IsMinimizer (PF A b F) (Phi q c) z →
      Phi q c z = Phi q c xs ∧ (∀ e ∈ Nset q, z e = xs e) ∧
        ∀ e, e ∉ F → 0 < z e → slack (castMat A) q c xs πs e = 0 := by sorry

end SepQPTardos.Main
