-- Prove2me | Theorems.Thm_SeqSubmod_Discrete_lemma_10
-- name    : SeqSubmod.Discrete.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:51.285621+00:00
-- url     : https://prove2.me/theorems/2dce8e00-4d93-423b-9c60-8265400b529c
-- title:
--   Lemma 10, p. 26 — for sequence-submodular u and nonempty B, some s ∈ S has u(s|A) ≥ u(B|A)/|B|
-- statement:
--   Let $\mathcal S$ be a set of actions and $u:\mathbb H^D(\mathcal S)\to\mathbb R$ a sequence-submodular discrete sequence function, i.e. $u(C\mid A)\ge u(C\mid B)$ whenever $A\prec B$, where $u(B\mid A)=u(A\perp B)-u(A)$ is the marginal value. Then for every sequence $A$ and every nonempty sequence $B$ there is a single action $s\in\mathcal S$ with
--   $$u(s\mid A)\ \ge\ \frac{1}{|B|}\,u(B\mid A).$$
--
--   In words: appending some single action after $A$ gains at least the average per-element gain of appending the whole sequence $B$. This is the discrete analogue of the paper's Lemma 9, and the step of the proof of Theorem 3 that compares a greedy choice with the optimal sequence.
--
--   **Formalization Note** The hypothesis $B\neq\emptyset$ is added: the paper states the lemma for all $B$, but $1/|B|$ is undefined at $|B|=0$, and in Lean $1/0=0$ would turn the claim into "some $s$ has $u(s\mid A)\ge 0$", which fails, e.g., for $u(A)=-|A|$ or for an empty action set. Only sequence-submodularity is assumed, as on the page; neither monotonicity nor finiteness of $\mathcal S$ is needed.
-- source:
--   Alaei, Makhdoumi & Malekian, Maximizing sequence-submodular functions and its application to online advertising, arXiv:1009.4153v4, p. 26, Lemma 10

import Mathlib
import Definitions.Def_SeqSubmod_Discrete_Setting

namespace SeqSubmod.Discrete
theorem lemma_10 {S : Type*} (u : List S → ℝ) (hu : IsSeqSubmodular u) (A B : List S)
    (hB : B ≠ []) :
    ∃ s : S, (1 / (B.length : ℝ)) * marginal u B A ≤ marginal u [s] A := by sorry
end SeqSubmod.Discrete
