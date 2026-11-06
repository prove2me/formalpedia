-- Prove2me | Theorems.Thm_WildeQIT_PinskerRefined_corollary_10_7_2
-- name    : WildeQIT.PinskerRefined.corollary_10_7_2
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:20:09.415398+00:00
-- url     : https://prove2.me/theorems/13557827-64cc-4ce5-b2db-b8cb66a22b5a
-- title:
--   Corollary 10.7.2 (Monotonicity of Relative Entropy) — $D(p\|q)\ge D(Np\|Nq)$ (corrected: saturation ⇒ $RNp=p$ needs $\mathrm{supp}(p)\subseteq\mathrm{supp}(q)$)
-- statement:
--   Let $p$ be a probability distribution on a finite alphabet $\mathcal X$, let $q:\mathcal X\to[0,\infty)$, and let $N(y|x)$ be a classical channel from $\mathcal X$ to a finite alphabet $\mathcal Y$. Write $(Np)(y)=\sum_x N(y|x)p(x)$ and $(Nq)(y)=\sum_x N(y|x)q(x)$. Then
--
--   $$
--   D(p\|q)\ge D(Np\|Nq). \tag{10.63}
--   $$
--
--   Moreover, let $R(x|y)$ be any channel from $\mathcal Y$ to $\mathcal X$ satisfying
--
--   $$
--   R(x|y)\,(Nq)(y)=N(y|x)\,q(x)\quad\text{for all }x,y, \tag{10.64}
--   $$
--
--   and let $(RNp)(x)=\sum_{y,x'}R(x|y)N(y|x')p(x')$. Then
--
--   1. if $RNp=p$, then $D(p\|q)=D(Np\|Nq)$;
--   2. if $\mathrm{supp}(p)\subseteq\mathrm{supp}(q)$ and $D(p\|q)=D(Np\|Nq)$, then $RNp=p$.
--
--   Here $D$ is the relative entropy of Definition 10.5.2, equal to $+\infty$ when $\mathrm{supp}(p)\not\subseteq\mathrm{supp}(q)$. The inequality is the data-processing inequality for relative entropy; the saturation clause identifies the Petz-type recovery channel $R$ as the one that undoes $N$ exactly when no relative entropy is lost.
--
--   **Formalization Note** Alphabets are finite types, as throughout the book; a random variable is represented by its distribution, and a triple $(X,Y,Z)$ by its joint distribution on $\mathcal X\times\mathcal Y\times\mathcal Z$. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits. $D$ is `relEntropy` (values in $\overline{\mathbb R}$), $Np$ is `N.apply p`, $Nq$ is `N.applyFun q`.
--
--   Differences from the source:
--
--   - correction: D(p‖q) = D(Np‖Nq) if and only if RNp = p, for every q : X → [0, ∞) → the direction D(p‖q) = D(Np‖Nq) ⇒ RNp = p is stated under supp(p) ⊆ supp(q); the direction RNp = p ⇒ equality and (10.63) are stated for every q ≥ 0; reason: counterexample with X = Y = {1, 2}, p = δ₁, q = δ₂, N = id, R(·|1) = R(·|2) = δ₂: (10.64) holds since (Nq)(1) = 0 = N(1|x) q(x), D(p‖q) = D(Np‖Nq) = +∞, but RNp = δ₂ ≠ p; supp(p) ⊆ supp(q) is the hypothesis of Theorem 10.8.4, from which the book derives this direction
--   - reading: "Let R be the channel defined by" (10.64) → every channel R satisfying (10.64); reason: (10.64) does not determine R(·|y) where (Nq)(y) = 0; the statement is asserted for each such R, which is the stronger reading
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Corollary 10.7.2, p. 303, Eqs. (10.63)–(10.64)

import Definitions.Def_WildeQIT_relEntropy
import Definitions.Def_WildeQIT_Channel

namespace WildeQIT.PinskerRefined

open WildeQIT

/-- **Corollary 10.7.2 (Monotonicity of Relative Entropy)**, Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 303, with the saturation
clause corrected. For a probability distribution `p` on `𝒳`, `q : 𝒳 → [0, ∞)` and a classical
channel `N(y|x)`, `D(p‖q) ≥ D(Np‖Nq)` (10.63). For every channel `R` satisfying (10.64),
`R(x|y) (Nq)(y) = N(y|x) q(x)`: if `RNp = p` then `D(p‖q) = D(Np‖Nq)`; and, when
`supp(p) ⊆ supp(q)`, `D(p‖q) = D(Np‖Nq)` implies `RNp = p`.

**Formalization Note** Alphabets are finite types (`Fintype`), as throughout the book; a random variable is represented by its distribution (`FinDist`), a triple `(X, Y, Z)` by its joint law on `α × β × γ` = `α × (β × γ)`. Entropies, mutual informations and relative entropies are the published `WildeQIT` definitions, in bits (`Real.logb 2`, `0 log 0 = 0`). `D` is the published `relEntropy` (`EReal`, `+∞` off support,
Definition 10.5.2); `Np` is `N.apply p`, `Nq` is `N.applyFun q`, and `RNp` is `R.apply (N.apply p)`,
whose mass at `x` is `∑_y R(x|y) ∑_{x'} N(y|x') p(x')`. Equations (10.64) do not determine `R(·|y)`
where `(Nq)(y) = 0`, so the clause is stated for every channel `R` satisfying them.

**Correction** As printed, "saturated iff `RNp = p`" fails in the direction "saturated ⇒ `RNp = p`":
on `𝒳 = 𝒴 = {1, 2}` take `p = δ₁`, `q = δ₂`, `N = id`, `R(·|1) = R(·|2) = δ₂`. Then (10.64) holds and
`D(p‖q) = D(Np‖Nq) = +∞`, but `RNp = δ₂ ≠ p`. That direction is stated under `supp(p) ⊆ supp(q)`,
the hypothesis of Theorem 10.8.4 (from which the book derives it); the other direction and (10.63)
hold for all `q`. -/
theorem corollary_10_7_2 {α β : Type} [Fintype α] [Fintype β]
    (p : FinDist α) (q : α → ℝ) (hq : ∀ x, 0 ≤ q x) (N : Channel α β) :
    relEntropy (N.apply p) (N.applyFun q) ≤ relEntropy p q ∧
      ∀ R : Channel β α, (∀ x y, (R y).prob x * N.applyFun q y = (N x).prob y * q x) →
        ((R.apply (N.apply p)).prob = p.prob →
            relEntropy p q = relEntropy (N.apply p) (N.applyFun q)) ∧
        (Function.support p.prob ⊆ Function.support q →
            relEntropy p q = relEntropy (N.apply p) (N.applyFun q) →
            (R.apply (N.apply p)).prob = p.prob) := by sorry

end WildeQIT.PinskerRefined
