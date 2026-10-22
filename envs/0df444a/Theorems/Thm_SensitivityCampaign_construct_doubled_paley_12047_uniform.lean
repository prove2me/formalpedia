-- Prove2me | Theorems.Thm_SensitivityCampaign_construct_doubled_paley_12047_uniform
-- name    : SensitivityCampaign.construct_doubled_paley_12047_uniform
-- status  : Open
-- author  : @yousofy
-- created : 2026-10-21T16:55:50.313863+00:00
-- url     : https://prove2.me/theorems/549b1e69-92e3-440b-9051-e2983b252893
-- title:
--   Uniform growth for the doubled Paley construction
-- statement:
--   There is one positive natural constant $C$ such that for every natural $k$, including $0$, there exist a natural number $n$ and a total Boolean function $f$ on $n$ bits with $2^{8k}\le s(f)\le C\,2084175267334724^k$ and $12047^{8k}\le bs(f)$. The same $C$ works for all $k$; the function and its dimension may depend on $k$. This is an open construction target.
--
--   ### Independent read-back
--
--   The following was written by an independent Codex auditor given only the Lean code and dependency definitions. It is included here for review in the website editor.
--
--   There exists a positive natural number $C$ such that for every natural number $k$, including $k=0$, there exist a natural number $n$ and a Boolean-valued function $f:\{0,1\}^n\to\{0,1\}$ satisfying $2^{8k}\le s(f)\le C\cdot2084175267334724^k$ and $12047^{8k}\le b(f)$. Here, for an input $x$ and a subset $B\subseteq\{0,\ldots,n-1\}$, let $x^B$ be the input obtained by replacing $x_i$ with its Boolean negation for each $i\in B$ and leaving every other coordinate unchanged; $s(f)$ is the maximum, over all inputs $x$, of the number of coordinates $i$ for which $f(x^{\{i\}})\ne f(x)$; and $b(f)$ is the maximum, over all inputs $x$, of the cardinality of a family of pairwise disjoint, nonempty subsets $B$ of the coordinate set such that $f(x^B)\ne f(x)$ for every member $B$ of that family. The empty family is permitted and contributes zero, and the two maxima defining $s(f)$ and $b(f)$ need not occur at the same input. The constant $C$ is chosen once for all $k$, while $n$ and $f$ may depend on $k$. When $k=0$, the required bounds are $1\le s(f)\le C$ and $1\le b(f)$. Although the existential quantifier allows $n=0$, both quantities are zero for a function with no coordinates, so such a function cannot witness these inequalities for any $k$.
-- source:
--   Research handoff, 21 October 2026, proof_spec.tex, section “From finite profiles to an asymptotic separation”; best_bound_minimal_handoff.zip SHA-256 f215b7463d9bd0bf3290eeef78702ce9cf4834f31c01d2998fc81a384c8daf07.

import Mathlib
import Definitions.Def_SensitivityCampaign
open OAI.Paper320

theorem SensitivityCampaign.construct_doubled_paley_12047_uniform :
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      2 ^ (8*k) ≤ sensitivity f ∧
      sensitivity f ≤ C * 2084175267334724 ^ k ∧
      12047 ^ (8*k) ≤ blockSensitivity f := by sorry
