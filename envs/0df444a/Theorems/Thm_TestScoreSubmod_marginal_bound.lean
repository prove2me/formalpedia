-- Prove2me | Theorems.Thm_TestScoreSubmod_marginal_bound
-- name    : TestScoreSubmod.marginal_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:48:43.08899+00:00
-- url     : https://prove2.me/theorems/a50534c0-656b-46a4-9ff9-ac43c42d13a0
-- title:
--   Chain (25)–(29): $\Pr[g(Y_i)\le g(z)]\,(\mathbb E[g(z,X_i)]-g(z))\le a_i/k$
-- statement:
--   Let $k=r+1\le n=m+1$, let $g:\mathbb R_+^n\to\mathbb R_+$ be a measurable, symmetric, monotone submodular value function, and let $P_i$ be a probability law on $\mathbb R_+$ under which the $k$-fold replica has integrable value. Write $a_i^{(j)}=\mathbb E[g(X_i^{(1)},\dots,X_i^{(j)},0,\dots,0)]$ for $j$ independent replicas $X_i^{(t)}\sim P_i$, so that $a_i=a_i^{(k)}$.
--   Let $X_i\sim P_i$ and let $Y_i$ be a vector of $k-1$ further independent replicas. Let $z\in\mathbb R_+^{n-1}$ satisfy condition (b) of extended diminishing returns against every $y\in\mathbb R_+^{k-1}$ (padded with zeros): if $g(y)\le g(z)$ then $g(z,x)-g(z)\le g(y,x)-g(y)$ for all $x\ge0$. Then
--
--   $$
--   \Pr\bigl[g(Y_i)\le g(z)\bigr]\cdot\Bigl(\mathbb E\bigl[g(z,X_i)\bigr]-g(z)\Bigr)\le\frac{a_i}{k}.
--   $$
--
--   When the probability is positive this is (25)–(29): the marginal value $u(S^*\cup\{i\})-u(S^*)=\mathbb E[g(z,X_i)]-g(z)$ of item $i$ for the fictitious set $S^*$ with performances $z$ is at most $a_i/(k\Pr[g(Y_i)\le g(z)])$.
--
--   Differences from the source:
--
--   - encoding: the bound divided by Pr[g(Yᵢ) ≤ g(z)] → multiplied out by Pr[g(Yᵢ) ≤ g(z)]; reason: equivalent when the probability is positive; the printed form is undefined when it is 0
--   - generalization: z the vector of (21) with g(z) = min{c a_k, g^max_{k−1}} → every z ∈ ℝ₊ⁿ⁻¹ satisfying (21) against the vectors of ℝ₊ᵏ⁻¹; reason: only (21) is used; the paper's z is one such vector
--   - reading: u(S* ∪ {i}) − u(S*) for the fictitious set S* of (25) → E[g(z, Xᵢ)] − g(z); reason: the right-hand side of (25), which is how the paper evaluates the left-hand side
--   - generalization: stated inside the proof of Lemma 4, where g also has extended diminishing returns (here replaced by its consequence (21)) → no extended diminishing returns hypothesis; reason: not used by this step; the Lean statement specializes to the source's
--   - reading: φ, "a minimal element which does not change the function value" (p.11) → φ = 0 (mask, pad); reason: p.11 uses φ = 0 and the domain is ℝ₊; with φ > 0 and Xᵢ < φ possible u is not monotone, and if Xᵢ ≥ φ the shift g(x + φ) reduces to φ = 0
--   - encoding: E[g(·)] of a value function g → Measurable g; reason: what writing the expectations presupposes; excludes only cases where they are undefined
--   - encoding: the replication score aᵢ of (7) with k = r + 1 replicas → the (r + 1)-fold replica y ↦ g(pad y) is integrable; reason: what (7) presupposes; the integrability of the other expectations follows from it
--   - encoding: k replicas, k − 1 replicas, 0 < k ≤ n; nonnegative Xᵢ ∼ Pᵢ; g : ℝ₊ⁿ → ℝ₊ → k = r + 1 with r + 1 ≤ m + 1 = n; Pᵢ a probability measure on ℝ≥0; replicas as Measure.pi over Fin r; 0 ≤ g x; reason: avoids natural-number subtraction k − 1; same instances
-- source:
--   Sekar, Vojnovic, Yun, A Test Score Based Approach to Stochastic Submodular Optimization, arXiv:1605.07172v4, Appendix D, proof of the upper bound of Lemma 4, (25)–(29), p.37

import Mathlib
import Definitions.Def_TestScoreSubmod_IsSubmodularValue
import Definitions.Def_TestScoreSubmod_IsSymmetricValue
import Definitions.Def_TestScoreSubmod_repScore

open scoped NNReal
open MeasureTheory

namespace TestScoreSubmod

/-- **The chain (25)–(29)** (Sekar, Vojnovic, Yun, arXiv:1605.07172v4, Appendix D, upper bound of
Lemma 4, (25)–(29), p.37: "u(S* ∪ {i}) − u(S*) = E[g(z, Xᵢ) − g(z)] = … ≤ (1/Pr[g(Yᵢ) ≤ g(z)]) (aᵢ/k)").

Let `k = r + 1 ≤ n = m + 1`, `g` a nonnegative, measurable, symmetric, monotone submodular
value function, `Pᵢ` a probability law on `ℝ₊` with integrable `k`-fold replica, `Xᵢ ∼ Pᵢ`,
and `Yᵢ` a vector of `k − 1` independent replicas of `Xᵢ`. Let `z ∈ ℝ₊^{n−1}` satisfy condition (b) of
extended diminishing returns against every `y ∈ ℝ₊^{k−1}` (padded with `0`): if
`g(y) ≤ g(z)` then `g(z, x) − g(z) ≤ g(y, x) − g(y)` for all `x ≥ 0`. Then

`Pr[g(Yᵢ) ≤ g(z)] · (E[g(z, Xᵢ)] − g(z)) ≤ aᵢ / k`.

**Formalization Note** The printed chain divides by `Pr[g(Yᵢ) ≤ g(z)]`; the statement is
multiplied out, so it also holds when that probability is `0`. `g(z, t)` is `g (Fin.snoc z t)`,
`g(z) = g(z, 0)`, and `g(y)` for `y ∈ ℝ₊^{k−1}` is `g (Fin.snoc (pad y) 0)`; `φ = 0`. -/
theorem marginal_bound {m r : ℕ} (hr : r + 1 ≤ m + 1)
    (g : (Fin (m + 1) → ℝ≥0) → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hmeas : Measurable g)
    (hsym : IsSymmetricValue g) (hmono : Monotone g) (hsub : IsSubmodularValue g)
    (P : Fin (m + 1) → Measure ℝ≥0) (i : Fin (m + 1)) [IsProbabilityMeasure (P i)]
    (hint : Integrable (fun y : Fin (r + 1) → ℝ≥0 => g (pad y))
      (Measure.pi fun _ : Fin (r + 1) => P i))
    (z : Fin m → ℝ≥0)
    (hz : ∀ y : Fin r → ℝ≥0,
      g (Fin.snoc (α := fun _ => ℝ≥0) (pad y) 0) ≤ g (Fin.snoc (α := fun _ => ℝ≥0) z 0) →
      ∀ x : ℝ≥0,
        g (Fin.snoc (α := fun _ => ℝ≥0) z x) - g (Fin.snoc (α := fun _ => ℝ≥0) z 0) ≤
          g (Fin.snoc (α := fun _ => ℝ≥0) (pad y) x) - g (Fin.snoc (α := fun _ => ℝ≥0) (pad y) 0)) :
    ((Measure.pi fun _ : Fin r => P i)
        {Y | g (Fin.snoc (α := fun _ => ℝ≥0) (pad Y) 0) ≤ g (Fin.snoc (α := fun _ => ℝ≥0) z 0)}).toReal *
        ((∫ t, g (Fin.snoc (α := fun _ => ℝ≥0) z t) ∂(P i)) - g (Fin.snoc (α := fun _ => ℝ≥0) z 0)) ≤
      repScore g P (r + 1) i / ((r : ℝ) + 1) := by sorry

end TestScoreSubmod
