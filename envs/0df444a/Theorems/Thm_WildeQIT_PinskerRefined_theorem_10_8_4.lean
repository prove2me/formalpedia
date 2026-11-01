-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_theorem_10_8_4
-- name    : WildeQIT.PinskerRefined.theorem_10_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:20:14.221991+00:00
-- url     : https://prove2.me/theorems/d05f6a3b-6ce7-4629-bd79-d9612cedb7c1
-- title:
--   Theorem 10.8.4 (Refined Monotonicity of Relative Entropy) — $D(p\|q)-D(Np\|Nq)\ge D(p\|RNp)$
-- statement:
--   Let $p$ be a probability distribution on a finite alphabet $\mathcal X$, let $q:\mathcal X\to[0,\infty)$ satisfy $\mathrm{supp}(p)\subseteq\mathrm{supp}(q)$, and let $N(y|x)$ be a classical channel from $\mathcal X$ to a finite alphabet $\mathcal Y$, with $(Np)(y)=\sum_x N(y|x)p(x)$ and $(Nq)(y)=\sum_x N(y|x)q(x)$. Let $R(x|y)$ be a recovery channel from $\mathcal Y$ to $\mathcal X$ defined by
--
--   $$
--   R(x|y)\,(Nq)(y)=N(y|x)\,q(x)\quad\text{for all }x,y, \tag{10.165}
--   $$
--
--   and let $(RNp)(x)=\sum_{y,x'}R(x|y)N(y|x')p(x')$. Then
--
--   $$
--   D(p\|q)-D(Np\|Nq)\ge D(p\|RNp). \tag{10.164}
--   $$
--
--   If the loss of relative entropy under $N$ is small, then the recovery channel $R$ (Bayes' rule when $q$ is a probability distribution) nearly restores $p$ from $Np$. It gives the saturation clause of Corollary 10.7.2.
--
--   **Formalization Note** $D$ is `relEntropy` (bits, extended reals); under $\mathrm{supp}(p)\subseteq\mathrm{supp}(q)$ the three relative entropies are finite, so the difference is the real difference. The theorem holds for every channel $R$ satisfying (10.165).
--
--   Differences from the source:
--
--   - reading: "the recovery channel R(x|y) … is defined by" (10.165) → every channel R satisfying (10.165); reason: (10.165) does not determine R(·|y) where (Nq)(y) = 0; the statement is asserted for each such R, which is the stronger reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.8.4, p. 315, Eqs. (10.164)–(10.165)

import Definitions.Def_WildeQIT_relEntropy
import Definitions.Def_WildeQIT_Channel

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Theorem 10.8.4 (Refined Monotonicity of Relative Entropy)**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 315: let `p` be a
probability distribution on a finite alphabet `𝒳`, `q : 𝒳 → [0, ∞)` with `supp(p) ⊆ supp(q)`, and
`N(y|x)` a classical channel. For the recovery channel `R(x|y)` defined by (10.165),
`R(x|y) (Nq)(y) = N(y|x) q(x)`, `D(p‖q) − D(Np‖Nq) ≥ D(p‖RNp)` (10.164).

**Formalization Note** `D` is the published `relEntropy` (bits, `EReal`, `+∞` off support,
Definition 10.5.2); `Np` is `N.apply p`, `Nq` is `N.applyFun q`, and `RNp` is `R.apply (N.apply p)`,
with mass `∑_{y,x'} R(x|y) N(y|x') p(x')` at `x`. Equations (10.165) do not determine `R(·|y)` where
`(Nq)(y) = 0`, so the theorem is stated for every channel `R` satisfying them. Under
`supp(p) ⊆ supp(q)` all three relative entropies are finite, so the `EReal` difference is the real
difference. -/
theorem theorem_10_8_4 {α β : Type} [Fintype α] [Fintype β]
    (p : FinDist α) (q : α → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hsupp : Function.support p.prob ⊆ Function.support q)
    (N : Channel α β) (R : Channel β α)
    (hR : ∀ x y, (R y).prob x * N.applyFun q y = (N x).prob y * q x) :
    relEntropy p (R.apply (N.apply p)).prob ≤
      relEntropy p q - relEntropy (N.apply p) (N.applyFun q) := by sorry

end WildeQIT.PinskerRefined
