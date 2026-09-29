-- Prove2me | Theorems.Thm_RobustMDP_Discounted_lemma_two
-- name    : RobustMDP.Discounted.lemma_two
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:58:02.283504+00:00
-- url     : https://prove2.me/theorems/926f9c92-11e7-44ba-93bd-7130e1d10a2a
-- title:
--   Lemma 2, p. 785 — a monotone contraction solves the program $\max q^T v$ s.t. $v \le g(v)$
-- statement:
--   Let $q \in \mathbb R^n_+$ and let $g : \mathbb R^n \to \mathbb R^n$ be componentwise nondecreasing and a contraction for the sup norm: there is $K < 1$ with $\|g(u) - g(v)\|_\infty \le K \|u - v\|_\infty$ for all $u, v$. Consider the problem
--   $$\max_v \; q^T v \quad \text{s.t.} \quad v \le g(v), \tag{24}$$
--   with inequalities understood componentwise. Then $g$ has a unique fixed point $v_\infty$, and
--   1. $q^T v_\infty$ is the optimal value of (24), attained at $v_\infty$;
--   2. every feasible $v$ satisfies $v \le v_\infty$ componentwise;
--   3. if moreover $q_i > 0$ for every $i$, then $v_\infty$ is the unique optimizer of (24).
--
--   This is the tool that turns the linear and nonlinear programs (26)–(28) of the proof of Theorem 3 into fixed-point equations.
--
--   **Formalization Note** As printed, the lemma asserts a unique optimizer for every $q \in \mathbb R^n_+$. That is false when $q$ has a zero entry: with $g \equiv 0$ and $q = (1, 0)$, every $v = (0, -t)$, $t \ge 0$, is optimal. Uniqueness of the optimizer is therefore stated under $q > 0$; the optimal value, the bound $v \le v_\infty$ and uniqueness of the fixed point hold for all $q \ge 0$. The printed hypothesis "if the above problem is feasible" is automatic, since $v_\infty$ is feasible. "Contractive" is read as a sup-norm contraction with constant $K < 1$ (`ContractingWith`), which is what the proof of Theorem 3 establishes.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 785, Lemma 2 (Eq. (24))

import Mathlib

namespace RobustMDP.Discounted

/-- Lemma 2 (Nilim–El Ghaoui 2005, p. 785), in the corrected form the proof of Theorem 3 uses.
Let `q ∈ ℝⁿ₊` and let `g : ℝⁿ → ℝⁿ` be componentwise nondecreasing and a contraction in the sup
norm (`ContractingWith K g`, i.e. `K < 1` and `g` is `K`-Lipschitz for the sup metric of
`Fin n → ℝ`). Consider problem (24): maximise `qᵀ v` subject to `v ≤ g(v)` componentwise.
Then `g` has a unique fixed point `v_∞`, and
1. `qᵀ v_∞` is the maximum of (24) (attained at the feasible point `v_∞`);
2. every feasible `v` satisfies `v ≤ v_∞` componentwise;
3. if moreover `q > 0` componentwise, `v_∞` is the only optimizer of (24).

As printed, the lemma claims a unique optimizer for every `q ∈ ℝⁿ₊`; that fails when `q` has zero
entries (`g ≡ 0`, `q = (1, 0)`: every `(0, -t)`, `t ≥ 0`, is optimal), so uniqueness of the
optimizer is stated under `q > 0`. The printed feasibility hypothesis is automatic. -/
theorem lemma_two {n : ℕ} (q : Fin n → ℝ) (hq : 0 ≤ q) (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hmono : Monotone g) (K : NNReal) (hg : ContractingWith K g) :
    ∃ vinf : Fin n → ℝ,
      g vinf = vinf ∧ (∀ w, g w = w → w = vinf) ∧
      IsGreatest ((fun v : Fin n → ℝ => ∑ i, q i * v i) '' {v | v ≤ g v})
        (∑ i, q i * vinf i) ∧
      (∀ v, v ≤ g v → v ≤ vinf) ∧
      ((∀ i, 0 < q i) →
        ∀ v, v ≤ g v → ∑ i, q i * v i = ∑ i, q i * vinf i → v = vinf) := by sorry

end RobustMDP.Discounted
