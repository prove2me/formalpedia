-- Prove2me | Theorems.Thm_SATotalCoeffLB_theorem_3_functional_bound
-- name    : SATotalCoeffLB.theorem_3_functional_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:21:43.93355+00:00
-- url     : https://prove2.me/theorems/14f8090c-a595-4da1-859f-80efc10c1ea8
-- title:
--   Proof of Theorem 3 — applying $\tilde L$ to (25) gives $\sum_e\|C_e\|_1\ge 2/\varepsilon$
-- statement:
--   Let $E \subseteq \binom{[n]}{2}$, $H \in \mathbb F_2^{t\times E}$, signs $s$, $\varepsilon > 0$ and $k \in \mathbb N$. Let $\tilde L$ be a linear functional on $\mathbb R[X,Y,T]/\langle y^2-1\rangle$ such that $\tilde L(1) = 1$, $\tilde L(D q_e) = 0$ for every $e \in E$ and polynomial $D$, $|\tilde L(C p_e)| \le \frac{\varepsilon}{2}\|C\|_1$ for every pair $e$ and polynomial $C$, and $\tilde L$ is nonnegative on every nonnegative $k$-junta. Then every identity
--
--   $$
--   -1 = \sum_j h_j + \sum_{e\in\binom{[n]}{2}} C_e p_e + \sum_{e \in E} D_e q_e \tag{25}
--   $$
--
--   with each $h_j$ a nonnegative $k$-junta satisfies
--
--   $$
--   \sum_{e\in\binom{[n]}{2}} \|C_e\|_1 \ge \frac{2}{\varepsilon}.
--   $$
--
--   On the page this is the computation $-1 = \sum_j \tilde L(h_j) + \sum_e \tilde L(C_e p_e) \ge -\frac{\varepsilon}{2}\sum_e \|C_e\|_1$ for the functional of Lemma 19, where $2/\varepsilon = \frac23 2^{\tau n/2}$.
--
--   Differences from the source:
--   - generalization: the functional $\tilde L$ of Lemma 19, with $\varepsilon = 3\cdot2^{-\tau n/2}$ → any linear functional with the four properties of Lemma 19 for a fixed $k$, and any $\varepsilon > 0$; reason: the computation uses only these properties; for the page's $\varepsilon$, $2/\varepsilon = \frac23 2^{\tau n/2}$ is the printed value
--   - encoding: a finite family $(h_j)_j$; multipliers $C_e$ for all pairs and $D_e$ for $e \in E$ → $h$ indexed by $\{0,\dots,r-1\}$; $C$ a function on all pairs, $D$ a function on $E$; reason: same identities
--   - encoding: the Boolean quotient ring $\mathbb R[\text{variables}]/\langle y^2-1\rangle$ → real functions on bit vectors, variable $v$ evaluating to $(-1)^{x_v}$ (`CubeFn`); reason: for finitely many variables evaluation on the $\pm1$ cube is a ring isomorphism; same identities
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.4, Proof of Theorem 3, p.56

import Mathlib
import Definitions.Def_SATotalCoeffLB_andCheck
import Definitions.Def_SATotalCoeffLB_parityCheckH
import Definitions.Def_SATotalCoeffLB_coeffNorm
import Definitions.Def_SATotalCoeffLB_DependsOnAtMost

namespace SATotalCoeffLB

/-- **Proof of Theorem 3, the functional bound**, p.56 of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178).

Let `E` be a set of pairs on `[n]`, `H ∈ F₂^{t×E}`, `s` signs, `ε > 0` and `k ∈ ℕ`, and let `L̃` be a
linear functional on `ℝ[X, Y, T]/⟨y² − 1⟩` with `L̃(1) = 1`, `L̃(D q_e) = 0` for `e ∈ E`,
`|L̃(C p_e)| ≤ (ε/2)‖C‖₁` for every pair `e`, and `L̃ ≥ 0` on nonnegative `k`-juntas (the properties of
Lemma 19). Then every identity (25),
`−1 = ∑_j h_j + ∑_{e ∈ ([n] choose 2)} C_e p_e + ∑_{e ∈ E} D_e q_e`, with each `h_j` a nonnegative
`k`-junta, satisfies `∑_e ‖C_e‖₁ ≥ 2/ε`.

**Formalization Note** The functional is a hypothesis; the page applies the `L̃` of Lemma 19, for
which `2/ε = (2/3)·2^{τn/2}`. The family `(h_j)` is indexed by `Fin r`. -/
theorem theorem_3_functional_bound (n t : ℕ) (E : Finset (Pair n))
    (H : Matrix (Fin t) E (ZMod 2)) (s : E → ℝ) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
    (Lt : CubeFn (Var n t) →ₗ[ℝ] ℝ) (h1 : Lt 1 = 1)
    (hq : ∀ (e : E) (D : CubeFn (Var n t)), Lt (D * parityCheckH H s e) = 0)
    (hp : ∀ (e : Pair n) (Cf : CubeFn (Var n t)), |Lt (Cf * andCheck t e)| ≤ ε / 2 * coeffNorm Cf)
    (hpos : ∀ h : CubeFn (Var n t), DependsOnAtMost k h → (∀ x, 0 ≤ h x) → 0 ≤ Lt h)
    (r : ℕ) (h : Fin r → CubeFn (Var n t)) (C : Pair n → CubeFn (Var n t))
    (D : E → CubeFn (Var n t))
    (hh : ∀ j, DependsOnAtMost k (h j) ∧ ∀ x, 0 ≤ h j x)
    (hid : (-1 : CubeFn (Var n t)) =
      ∑ j, h j + ∑ e, C e * andCheck t e + ∑ e, D e * parityCheckH H s e) :
    2 / ε ≤ ∑ e, coeffNorm (C e) := by sorry

end SATotalCoeffLB
