-- Prove2me | Theorems.Thm_WildeQIT_ZhangAudenaert_fano_inequality
-- name    : WildeQIT.ZhangAudenaert.fano_inequality
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:56:46.74851+00:00
-- url     : https://prove2.me/theorems/e4e8fb83-f7ea-42ed-be32-0a7463973da3
-- title:
--   Theorem 10.7.3 (Fano's Inequality): $H(X|Y)\le H(X|\hat X)\le h_2(p_e)+p_e\log(|\mathcal X|-1)$, its limit and sharpness
-- statement:
--   Let $X$ take values in a finite alphabet $\mathcal X$, let $Y$ take values in a finite alphabet $\mathcal Y$, and let $\hat X$, an estimate of $X$, take values in $\mathcal X$, such that $X\to Y\to\hat X$ is a Markov chain. Let $p_e\equiv\Pr\{\hat X\neq X\}$ be the probability of error and $h_2$ the binary entropy. Then:
--
--   1. (10.79) The information lost in the channel noise is bounded by a function of the error probability:
--   $$
--   H(X|Y)\le H(X|\hat X)\le h_2(p_e)+p_e\log(|\mathcal X|-1).
--   $$
--   2. (10.80) For fixed $|\mathcal X|$,
--   $$
--   \lim_{p_e\to0}\bigl[h_2(p_e)+p_e\log(|\mathcal X|-1)\bigr]=0 .
--   $$
--   3. The bound is sharp: for every $\varepsilon\in[0,1]$ (and $|\mathcal X|\ge2$, unless $\varepsilon=0$) there are random variables $X,Y,\hat X$ on $\mathcal X$ forming a Markov chain $X\to Y\to\hat X$ with $\Pr\{\hat X\neq X\}=\varepsilon$ and
--   $$
--   H(X|Y)=h_2(\varepsilon)+\varepsilon\log(|\mathcal X|-1),
--   $$
--   so that both inequalities in (10.79) are equalities.
--
--   Fano's inequality is the standard tool for converse proofs of coding theorems: a small error probability forces a small equivocation $H(X|Y)$. It is also the main step in the proof of the Zhang–Audenaert inequality.
--
--   **Formalization Note** The three random variables are represented by the joint distribution of $(X,Y,\hat X)$ on $\mathcal X\times\mathcal Y\times\mathcal X$; the Markov property is the published `FinDist.IsMarkovChain`; $p_e$ is the mission's `probNe` of the $(X,\hat X)$ marginal. Logarithms are base $2$, and $\log(|\mathcal X|-1)$ is computed with real subtraction, which is $\log 0=0$ when $|\mathcal X|=1$ (then $p_e=0$).
--
--   Differences from the source:
--   - reading: there is a choice of random variables X and Y that saturates it → for every ε ∈ [0,1], with |𝒳| ≥ 2 or ε = 0, a Markov chain X → Y → X̂ on 𝒳 with Pr{X̂ ≠ X} = ε and H(X|Y) = h₂(ε) + ε log(|𝒳| − 1); reason: the literal ∃ is met by the trivial ε = 0 instance; the book's proof (p. 306) constructs the saturating chain for every ε ∈ [0,1] with X̂ = Y, which is the stronger reading; ε > 0 needs a second letter
--   - generalization: lim_{pe→0} h2(pe) + pe log(|X| − 1) = 0, pe a probability → two-sided limit Tendsto … (nhds 0) (nhds 0) of the real function pe ↦ h₂(pe) + pe log(|X| − 1); reason: the two-sided limit implies the limit through pe ≥ 0, which is the book's
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 10.7.3, eqs. (10.79)–(10.80), p. 305; sharpness construction eq. (10.91), p. 306

import Mathlib
import Definitions.Def_WildeQIT_condEntropy
import Definitions.Def_WildeQIT_binaryEntropy
import Definitions.Def_WildeQIT_IsMarkovChain
import Definitions.Def_WildeQIT_ZhangAudenaert_probNe

namespace WildeQIT.ZhangAudenaert

/-- **Theorem 10.7.3 (Fano's Inequality).**
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 10.7.3,
(10.79)–(10.80), p. 305 (sharpness construction (10.91), p. 306): if `X → Y → X̂` is a Markov
chain, with `X̂` an estimate of `X`, and `p_e ≡ Pr{X̂ ≠ X}`, then
`H(X|Y) ≤ H(X|X̂) ≤ h₂(p_e) + p_e log(|𝒳| − 1)`; moreover
`lim_{p_e → 0} h₂(p_e) + p_e log(|𝒳| − 1) = 0`, and the bound is sharp: some choice of `X` and
`Y` saturates it.

The statement has three parts:
1. for every finite alphabet `β` of `Y` and every joint distribution `p` of `(X, Y, X̂)` on
   `α × β × α` forming a Markov chain, `H(X|Y) ≤ H(X|X̂) ≤ h₂(p_e) + p_e log(|α| − 1)`;
2. the limit (10.80), with `|α|` fixed, stated as a two-sided limit at `0` (which contains the
   limit through probabilities `p_e ≥ 0`);
3. sharpness: for every `ε ∈ [0, 1]` there is a Markov chain `X → Y → X̂` (with `Y` and `X̂`
   in the alphabet `α`) whose error probability is `ε` and whose `H(X|Y)` equals the bound, so
   both inequalities of (10.79) are equalities. This needs `|α| ≥ 2` unless `ε = 0`.

**Formalization Note.** Random variables are represented by their joint distribution
`p : FinDist (α × β × α)` of `(X, Y, X̂)`; `H(X|Y) = condEntropy p.margXY`,
`H(X|X̂) = condEntropy p.margXZ`, `p_e = probNe p.margXZ`. Entropies are in bits. The
logarithm `log(|α| − 1)` is `Real.logb 2 ((Fintype.card α : ℝ) − 1)`, with real subtraction;
at `|α| = 1` it is `Real.logb 2 0 = 0`, and then `p_e = 0`. -/
theorem fano_inequality {α : Type} [Fintype α] [DecidableEq α] :
    (∀ (β : Type) [Fintype β] (p : FinDist (α × β × α)), p.IsMarkovChain →
        condEntropy p.margXY ≤ condEntropy p.margXZ ∧
          condEntropy p.margXZ ≤ binaryEntropy (probNe p.margXZ) +
            probNe p.margXZ * Real.logb 2 ((Fintype.card α : ℝ) - 1)) ∧
      Filter.Tendsto
        (fun pe : ℝ => binaryEntropy pe + pe * Real.logb 2 ((Fintype.card α : ℝ) - 1))
        (nhds 0) (nhds 0) ∧
      (Nonempty α → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → (2 ≤ Fintype.card α ∨ ε = 0) →
        ∃ p : FinDist (α × α × α), p.IsMarkovChain ∧ probNe p.margXZ = ε ∧
          condEntropy p.margXY = binaryEntropy ε + ε * Real.logb 2 ((Fintype.card α : ℝ) - 1)) := by sorry

end WildeQIT.ZhangAudenaert
